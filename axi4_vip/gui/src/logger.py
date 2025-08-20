#!/usr/bin/env python3
"""
Comprehensive Logging System for AXI4 Generator GUI
Provides detailed logging for debugging and tracing issues
"""

import os
import logging
import logging.handlers
from pathlib import Path
from datetime import datetime
import threading
import queue
import traceback


class GuiLogHandler(logging.Handler):
    """Custom log handler that can send logs to GUI components"""
    
    def __init__(self):
        super().__init__()
        self.log_queue = queue.Queue()
        self.gui_callbacks = []
    
    def emit(self, record):
        """Emit log record to queue and GUI callbacks"""
        try:
            msg = self.format(record)
            self.log_queue.put((record.levelno, msg, record.created))
            
            # Send to GUI callbacks
            for callback in self.gui_callbacks:
                try:
                    callback(record.levelno, msg, record.created)
                except Exception:
                    pass  # Don't let GUI callback errors break logging
        except Exception:
            self.handleError(record)
    
    def add_gui_callback(self, callback):
        """Add GUI callback for real-time log display"""
        self.gui_callbacks.append(callback)
    
    def get_recent_logs(self, count=100):
        """Get recent log messages from queue"""
        logs = []
        try:
            while len(logs) < count:
                level, msg, timestamp = self.log_queue.get_nowait()
                logs.append((level, msg, timestamp))
        except queue.Empty:
            pass
        return logs


class BatchLogger:
    """Specialized logger for batch operations"""
    
    def __init__(self, batch_name, log_dir="logs"):
        self.batch_name = batch_name
        self.log_dir = Path(log_dir)
        self.log_dir.mkdir(exist_ok=True)
        
        # Create batch-specific log file
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.log_file = self.log_dir / f"batch_{batch_name}_{timestamp}.log"
        
        # Setup batch logger
        self.logger = logging.getLogger(f"batch.{batch_name}")
        self.logger.setLevel(logging.DEBUG)
        
        # File handler for batch logs
        file_handler = logging.FileHandler(self.log_file)
        file_handler.setLevel(logging.DEBUG)
        
        # Detailed formatter for batch logs
        formatter = logging.Formatter(
            '%(asctime)s - %(name)s - %(levelname)s - %(funcName)s:%(lineno)d - %(message)s'
        )
        file_handler.setFormatter(formatter)
        
        if not self.logger.handlers:
            self.logger.addHandler(file_handler)
        
        self.start_time = datetime.now()
        self.errors = []
        self.warnings = []
        
        self.logger.info(f"=== BATCH STARTED: {batch_name} ===")
    
    def info(self, message):
        """Log info message"""
        self.logger.info(message)
    
    def warning(self, message):
        """Log warning message"""
        self.warnings.append(message)
        self.logger.warning(message)
    
    def error(self, message, exc_info=None):
        """Log error message with optional exception info"""
        self.errors.append(message)
        self.logger.error(message, exc_info=exc_info)
    
    def exception(self, message):
        """Log exception with traceback"""
        exc_msg = f"{message}\n{traceback.format_exc()}"
        self.errors.append(exc_msg)
        self.logger.exception(message)
    
    def finish(self, success=True):
        """Finish batch logging with summary"""
        duration = datetime.now() - self.start_time
        
        if success:
            self.logger.info(f"=== BATCH COMPLETED SUCCESSFULLY ===")
        else:
            self.logger.error(f"=== BATCH FAILED ===")
        
        self.logger.info(f"Duration: {duration}")
        self.logger.info(f"Warnings: {len(self.warnings)}")
        self.logger.info(f"Errors: {len(self.errors)}")
        
        if self.warnings:
            self.logger.info("Warnings summary:")
            for i, warning in enumerate(self.warnings[:5], 1):
                self.logger.info(f"  {i}. {warning}")
        
        if self.errors:
            self.logger.info("Errors summary:")
            for i, error in enumerate(self.errors[:5], 1):
                self.logger.info(f"  {i}. {error}")
        
        return {
            'success': success,
            'duration': duration.total_seconds(),
            'warnings': len(self.warnings),
            'errors': len(self.errors),
            'log_file': str(self.log_file)
        }


class AppLogger:
    """Main application logger setup"""
    
    _instance = None
    _lock = threading.Lock()
    
    def __new__(cls):
        if cls._instance is None:
            with cls._lock:
                if cls._instance is None:
                    cls._instance = super().__new__(cls)
        return cls._instance
    
    def __init__(self):
        if hasattr(self, 'initialized'):
            return
        
        self.initialized = True
        self.log_dir = Path("logs")
        self.log_dir.mkdir(exist_ok=True)
        
        # Setup main application logger
        self.logger = logging.getLogger('axi4_gui')
        self.logger.setLevel(logging.DEBUG)
        
        # Clear any existing handlers
        self.logger.handlers.clear()
        
        # Console handler
        console_handler = logging.StreamHandler()
        console_handler.setLevel(logging.INFO)
        console_formatter = logging.Formatter(
            '%(asctime)s - %(levelname)s - %(message)s',
            datefmt='%H:%M:%S'
        )
        console_handler.setFormatter(console_formatter)
        
        # File handler with rotation
        file_handler = logging.handlers.RotatingFileHandler(
            self.log_dir / "app.log",
            maxBytes=10*1024*1024,  # 10MB
            backupCount=5
        )
        file_handler.setLevel(logging.DEBUG)
        file_formatter = logging.Formatter(
            '%(asctime)s - %(name)s - %(levelname)s - %(funcName)s:%(lineno)d - %(message)s'
        )
        file_handler.setFormatter(file_formatter)
        
        # GUI handler
        self.gui_handler = GuiLogHandler()
        self.gui_handler.setLevel(logging.INFO)
        self.gui_handler.setFormatter(console_formatter)
        
        # Add handlers
        self.logger.addHandler(console_handler)
        self.logger.addHandler(file_handler)
        self.logger.addHandler(self.gui_handler)
        
        # Prevent propagation to root logger
        self.logger.propagate = False
        
        self.logger.info("=== AXI4 Generator GUI Started ===")
    
    def get_logger(self, name=None):
        """Get logger instance"""
        if name:
            return logging.getLogger(f'axi4_gui.{name}')
        return self.logger
    
    def add_gui_callback(self, callback):
        """Add GUI callback for real-time log display"""
        self.gui_handler.add_gui_callback(callback)
    
    def get_recent_logs(self, count=100):
        """Get recent log messages"""
        return self.gui_handler.get_recent_logs(count)
    
    def create_batch_logger(self, batch_name):
        """Create a new batch logger"""
        return BatchLogger(batch_name)


# Global logger instance
def get_logger(name=None):
    """Get application logger"""
    app_logger = AppLogger()
    return app_logger.get_logger(name)


def create_batch_logger(batch_name):
    """Create batch logger"""
    app_logger = AppLogger()
    return app_logger.create_batch_logger(batch_name)


def setup_gui_logging(gui_callback):
    """Setup GUI logging callback"""
    app_logger = AppLogger()
    app_logger.add_gui_callback(gui_callback)


def get_recent_logs(count=100):
    """Get recent log messages for GUI display"""
    app_logger = AppLogger()
    return app_logger.get_recent_logs(count)


# Function decorator for automatic logging
def log_function_call(func):
    """Decorator to automatically log function calls"""
    def wrapper(*args, **kwargs):
        logger = get_logger(func.__module__)
        logger.debug(f"Calling {func.__name__} with args={args[:2]}... kwargs={list(kwargs.keys())}")
        try:
            result = func(*args, **kwargs)
            logger.debug(f"Completed {func.__name__} successfully")
            return result
        except Exception as e:
            logger.exception(f"Error in {func.__name__}: {e}")
            raise
    return wrapper


# Context manager for batch operations
class BatchOperation:
    """Context manager for batch operations with automatic logging"""
    
    def __init__(self, operation_name):
        self.operation_name = operation_name
        self.batch_logger = None
        self.success = False
    
    def __enter__(self):
        self.batch_logger = create_batch_logger(self.operation_name)
        return self.batch_logger
    
    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            self.success = True
        else:
            self.batch_logger.exception(f"Batch operation failed: {exc_val}")
        
        return self.batch_logger.finish(self.success)


# Example usage:
if __name__ == "__main__":
    # Test the logging system
    logger = get_logger("test")
    
    logger.info("Testing application logger")
    logger.warning("This is a warning")
    logger.error("This is an error")
    
    # Test batch logger
    with BatchOperation("test_batch") as batch:
        batch.info("Starting test operation")
        batch.warning("Test warning")
        batch.error("Test error")
        batch.info("Operation completed")
    
    print("Logging test completed - check logs/ directory")