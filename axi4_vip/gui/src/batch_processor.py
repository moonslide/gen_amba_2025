#!/usr/bin/env python3
"""
Background Batch Processing System for AXI4 Generator GUI
Supports running multiple RTL/VIP generation tasks in background
"""

import os
import threading
import queue
import time
import json
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Dict, Any, Callable, Optional
from datetime import datetime
import concurrent.futures

from bus_config import Project
from generator import Generator
from logger import BatchLogger, get_logger


@dataclass
class BatchTask:
    """Individual batch task configuration"""
    task_id: str
    task_type: str  # "rtl", "vip", "both"
    project: Project
    output_dir: str
    parameters: Dict[str, Any] = None
    priority: int = 0  # Higher number = higher priority
    
    def to_dict(self):
        """Convert to dictionary for serialization"""
        data = asdict(self)
        data['project'] = self.project.to_dict()
        return data
    
    @classmethod
    def from_dict(cls, data):
        """Create from dictionary"""
        project_data = data.pop('project')
        project = Project.from_dict(project_data)
        return cls(project=project, **data)


@dataclass
class BatchResult:
    """Batch task execution result"""
    task_id: str
    success: bool
    output_files: List[str]
    duration: float
    error_message: Optional[str] = None
    warnings: List[str] = None
    log_file: str = None
    
    def to_dict(self):
        """Convert to dictionary"""
        return asdict(self)


class BatchQueue:
    """Thread-safe batch task queue with priorities"""
    
    def __init__(self):
        self.queue = queue.PriorityQueue()
        self.active_tasks = {}
        self.completed_tasks = {}
        self.failed_tasks = {}
        self.lock = threading.Lock()
        self.logger = get_logger("batch_queue")
    
    def add_task(self, task: BatchTask):
        """Add task to queue"""
        with self.lock:
            # Use negative priority for max-heap behavior
            self.queue.put((-task.priority, time.time(), task))
            self.logger.info(f"Added task {task.task_id} to queue (priority: {task.priority})")
    
    def get_next_task(self, timeout=None):
        """Get next task from queue"""
        try:
            _, _, task = self.queue.get(timeout=timeout)
            with self.lock:
                self.active_tasks[task.task_id] = task
            return task
        except queue.Empty:
            return None
    
    def mark_completed(self, task_id: str, result: BatchResult):
        """Mark task as completed"""
        with self.lock:
            if task_id in self.active_tasks:
                del self.active_tasks[task_id]
            
            if result.success:
                self.completed_tasks[task_id] = result
                self.logger.info(f"Task {task_id} completed successfully")
            else:
                self.failed_tasks[task_id] = result
                self.logger.error(f"Task {task_id} failed: {result.error_message}")
    
    def get_status(self):
        """Get queue status"""
        with self.lock:
            return {
                'pending': self.queue.qsize(),
                'active': len(self.active_tasks),
                'completed': len(self.completed_tasks),
                'failed': len(self.failed_tasks)
            }
    
    def get_task_list(self):
        """Get list of all tasks"""
        with self.lock:
            return {
                'active': list(self.active_tasks.keys()),
                'completed': list(self.completed_tasks.keys()),
                'failed': list(self.failed_tasks.keys())
            }


class BatchWorker:
    """Background worker thread for processing batch tasks"""
    
    def __init__(self, worker_id: int, batch_queue: BatchQueue, status_callback: Callable = None):
        self.worker_id = worker_id
        self.batch_queue = batch_queue
        self.status_callback = status_callback
        self.running = False
        self.thread = None
        self.logger = get_logger(f"worker_{worker_id}")
    
    def start(self):
        """Start worker thread"""
        if not self.running:
            self.running = True
            self.thread = threading.Thread(target=self._worker_loop, daemon=True)
            self.thread.start()
            self.logger.info(f"Worker {self.worker_id} started")
    
    def stop(self):
        """Stop worker thread"""
        self.running = False
        if self.thread:
            self.thread.join(timeout=5)
        self.logger.info(f"Worker {self.worker_id} stopped")
    
    def _worker_loop(self):
        """Main worker loop"""
        while self.running:
            try:
                task = self.batch_queue.get_next_task(timeout=1.0)
                if task:
                    self.logger.info(f"Worker {self.worker_id} processing task {task.task_id}")
                    result = self._process_task(task)
                    self.batch_queue.mark_completed(task.task_id, result)
                    
                    # Notify GUI of status change
                    if self.status_callback:
                        self.status_callback(task.task_id, result)
                
            except Exception as e:
                self.logger.exception(f"Worker {self.worker_id} error: {e}")
    
    def _process_task(self, task: BatchTask) -> BatchResult:
        """Process a single batch task"""
        start_time = time.time()
        batch_logger = BatchLogger(f"task_{task.task_id}")
        
        try:
            batch_logger.info(f"Starting task {task.task_id} (type: {task.task_type})")
            batch_logger.info(f"Project: {task.project.name}")
            batch_logger.info(f"Masters: {len(task.project.masters)}, Slaves: {len(task.project.slaves)}")
            batch_logger.info(f"Output directory: {task.output_dir}")
            
            # Create output directory
            os.makedirs(task.output_dir, exist_ok=True)
            
            # Create generator
            generator = Generator(task.project)
            generator.output_dir = task.output_dir
            
            output_files = []
            warnings = []
            
            # Execute based on task type
            if task.task_type in ["rtl", "both"]:
                batch_logger.info("Generating RTL...")
                rtl_success, rtl_message = generator.generate_rtl()
                
                if rtl_success:
                    batch_logger.info("RTL generation completed successfully")
                    # Find generated RTL files
                    rtl_files = list(Path(task.output_dir).glob("*.v"))
                    output_files.extend([str(f) for f in rtl_files])
                else:
                    batch_logger.error(f"RTL generation failed: {rtl_message}")
                    if "warning" in rtl_message.lower():
                        warnings.append(rtl_message)
                    else:
                        raise Exception(f"RTL generation failed: {rtl_message}")
            
            if task.task_type in ["vip", "both"]:
                batch_logger.info("Generating VIP...")
                vip_success, vip_message = generator.generate_vip()
                
                if vip_success:
                    batch_logger.info("VIP generation completed successfully")
                    # Find generated VIP files
                    vip_files = list(Path(task.output_dir).rglob("*.sv"))
                    output_files.extend([str(f) for f in vip_files])
                else:
                    batch_logger.error(f"VIP generation failed: {vip_message}")
                    if "warning" in vip_message.lower():
                        warnings.append(vip_message)
                    else:
                        raise Exception(f"VIP generation failed: {vip_message}")
            
            duration = time.time() - start_time
            summary = batch_logger.finish(success=True)
            
            batch_logger.info(f"Task completed in {duration:.2f} seconds")
            batch_logger.info(f"Generated {len(output_files)} files")
            
            return BatchResult(
                task_id=task.task_id,
                success=True,
                output_files=output_files,
                duration=duration,
                warnings=warnings,
                log_file=summary['log_file']
            )
            
        except Exception as e:
            duration = time.time() - start_time
            error_msg = str(e)
            batch_logger.exception(f"Task failed: {error_msg}")
            summary = batch_logger.finish(success=False)
            
            return BatchResult(
                task_id=task.task_id,
                success=False,
                output_files=[],
                duration=duration,
                error_message=error_msg,
                log_file=summary['log_file']
            )


class BatchProcessor:
    """Main batch processing coordinator"""
    
    def __init__(self, max_workers: int = 2):
        self.max_workers = max_workers
        self.batch_queue = BatchQueue()
        self.workers = []
        self.status_callbacks = []
        self.logger = get_logger("batch_processor")
        self.running = False
        
        # Statistics
        self.stats = {
            'total_tasks': 0,
            'completed_tasks': 0,
            'failed_tasks': 0,
            'start_time': None
        }
    
    def start(self):
        """Start batch processor"""
        if not self.running:
            self.running = True
            self.stats['start_time'] = datetime.now()
            
            # Start worker threads
            for i in range(self.max_workers):
                worker = BatchWorker(i, self.batch_queue, self._task_completed_callback)
                worker.start()
                self.workers.append(worker)
            
            self.logger.info(f"Batch processor started with {self.max_workers} workers")
    
    def stop(self):
        """Stop batch processor"""
        if self.running:
            self.running = False
            
            # Stop all workers
            for worker in self.workers:
                worker.stop()
            self.workers.clear()
            
            self.logger.info("Batch processor stopped")
    
    def add_task(self, task: BatchTask):
        """Add task to processing queue"""
        self.batch_queue.add_task(task)
        self.stats['total_tasks'] += 1
        self.logger.info(f"Added task {task.task_id} to batch queue")
    
    def add_status_callback(self, callback: Callable):
        """Add callback for task status updates"""
        self.status_callbacks.append(callback)
    
    def _task_completed_callback(self, task_id: str, result: BatchResult):
        """Internal callback for task completion"""
        if result.success:
            self.stats['completed_tasks'] += 1
        else:
            self.stats['failed_tasks'] += 1
        
        # Notify all registered callbacks
        for callback in self.status_callbacks:
            try:
                callback(task_id, result)
            except Exception as e:
                self.logger.exception(f"Error in status callback: {e}")
    
    def get_status(self):
        """Get overall processor status"""
        queue_status = self.batch_queue.get_status()
        
        uptime = None
        if self.stats['start_time']:
            uptime = (datetime.now() - self.stats['start_time']).total_seconds()
        
        return {
            'running': self.running,
            'workers': len(self.workers),
            'uptime': uptime,
            'queue': queue_status,
            'stats': self.stats.copy()
        }
    
    def get_task_results(self):
        """Get all task results"""
        return {
            'completed': self.batch_queue.completed_tasks.copy(),
            'failed': self.batch_queue.failed_tasks.copy()
        }
    
    def create_batch_from_templates(self, templates: List[str], output_base_dir: str = "batch_output"):
        """Create batch tasks from template configurations"""
        from template_gallery import TemplateGallery
        
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        batch_dir = Path(output_base_dir) / f"batch_{timestamp}"
        
        tasks = []
        for i, template_name in enumerate(templates):
            try:
                # Create project from template
                if template_name == "axi_8x8":
                    project = TemplateGallery.create_axi_8x8()
                elif template_name == "axi_16x16":
                    project = TemplateGallery.create_axi_16x16()
                elif template_name == "axi_32x32":
                    project = TemplateGallery.create_axi_32x32()
                else:
                    self.logger.warning(f"Unknown template: {template_name}")
                    continue
                
                # Create batch task
                task = BatchTask(
                    task_id=f"batch_{timestamp}_{i:03d}_{template_name}",
                    task_type="both",  # Generate both RTL and VIP
                    project=project,
                    output_dir=str(batch_dir / template_name),
                    priority=i
                )
                
                tasks.append(task)
                self.add_task(task)
                
            except Exception as e:
                self.logger.exception(f"Error creating task for template {template_name}: {e}")
        
        self.logger.info(f"Created batch with {len(tasks)} tasks in {batch_dir}")
        return tasks


# Global batch processor instance
_batch_processor = None

def get_batch_processor(max_workers: int = 2):
    """Get global batch processor instance"""
    global _batch_processor
    if _batch_processor is None:
        _batch_processor = BatchProcessor(max_workers)
    return _batch_processor


# Example usage and testing
if __name__ == "__main__":
    import sys
    sys.path.append('.')
    
    # Test batch processing
    processor = get_batch_processor(max_workers=1)
    processor.start()
    
    def status_callback(task_id, result):
        print(f"Task {task_id} completed: {'SUCCESS' if result.success else 'FAILED'}")
        if result.success:
            print(f"  Generated {len(result.output_files)} files")
        else:
            print(f"  Error: {result.error_message}")
    
    processor.add_status_callback(status_callback)
    
    # Create batch from templates
    templates = ["axi_8x8"]
    tasks = processor.create_batch_from_templates(templates)
    
    print(f"Created {len(tasks)} tasks")
    print("Batch processing started...")
    
    # Wait for completion
    while True:
        status = processor.get_status()
        print(f"Queue: {status['queue']}")
        
        if status['queue']['pending'] == 0 and status['queue']['active'] == 0:
            break
        
        time.sleep(2)
    
    print("Batch processing completed!")
    processor.stop()