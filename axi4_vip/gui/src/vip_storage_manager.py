#!/usr/bin/env python3

"""
AXI4 VIP Storage Manager
Comprehensive storage management system to prevent unlimited storage growth in VIP GUI components.
Implements cleanup policies, archival, and size limits.
"""

import os
import sys
import sqlite3
import shutil
import gzip
import json
import time
import threading
from datetime import datetime, timedelta
from typing import Dict, List, Any, Optional, Tuple
from pathlib import Path
from dataclasses import dataclass
import logging
import psutil
import tempfile

@dataclass
class StoragePolicy:
    """Storage management policy configuration"""
    # Database policies
    max_test_results_age_days: int = 90
    max_test_results_count: int = 10000
    max_log_file_size_mb: int = 100
    
    # File system policies
    max_workspace_age_days: int = 7
    max_report_age_days: int = 30
    max_plot_age_days: int = 14
    max_total_storage_gb: int = 50
    
    # Archival policies
    enable_archival: bool = True
    archive_after_days: int = 30
    compress_archived: bool = True
    
    # Cleanup intervals
    cleanup_interval_hours: int = 6
    
    # Emergency cleanup thresholds
    emergency_cleanup_threshold_gb: int = 45
    emergency_cleanup_enabled: bool = True

class VIPStorageManager:
    """Manages storage usage and prevents unlimited growth"""
    
    def __init__(self, base_work_dir: str = "/tmp/vip_test_runs", 
                 policy: StoragePolicy = None):
        self.base_work_dir = Path(base_work_dir)
        self.policy = policy or StoragePolicy()
        
        # Setup logging
        self.logger = self._setup_logging()
        
        # Storage tracking
        self.storage_stats = {}
        self.cleanup_lock = threading.Lock()
        
        # Archive directory
        self.archive_dir = self.base_work_dir / "archive"
        self.archive_dir.mkdir(parents=True, exist_ok=True)
        
        # Start background cleanup thread
        self.cleanup_thread = None
        self.shutdown_event = threading.Event()
        self.start_background_cleanup()
        
    def _setup_logging(self) -> logging.Logger:
        """Setup logging for storage manager"""
        logger = logging.getLogger('VIPStorageManager')
        logger.setLevel(logging.INFO)
        
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            
        return logger
        
    def start_background_cleanup(self):
        """Start background cleanup thread"""
        if self.cleanup_thread is None or not self.cleanup_thread.is_alive():
            self.cleanup_thread = threading.Thread(
                target=self._background_cleanup_worker, 
                daemon=True
            )
            self.cleanup_thread.start()
            self.logger.info("Started background storage cleanup")
            
    def _background_cleanup_worker(self):
        """Background worker for periodic cleanup"""
        while not self.shutdown_event.is_set():
            try:
                self.logger.debug("Running background cleanup cycle")
                
                # Check storage usage
                total_usage = self.get_total_storage_usage()
                self.logger.debug(f"Total storage usage: {total_usage:.2f} GB")
                
                # Emergency cleanup if needed
                if (self.policy.emergency_cleanup_enabled and 
                    total_usage > self.policy.emergency_cleanup_threshold_gb):
                    self.logger.warning(f"Emergency cleanup triggered: {total_usage:.2f} GB")
                    self.emergency_cleanup()
                
                # Regular cleanup
                self.cleanup_old_data()
                
                # Wait for next cycle
                self.shutdown_event.wait(self.policy.cleanup_interval_hours * 3600)
                
            except Exception as e:
                self.logger.error(f"Error in background cleanup: {e}")
                # Wait a bit before retrying
                self.shutdown_event.wait(300)  # 5 minutes
                
    def get_total_storage_usage(self) -> float:
        """Get total storage usage in GB"""
        try:
            total_size = 0
            for root, dirs, files in os.walk(self.base_work_dir):
                for file in files:
                    file_path = os.path.join(root, file)
                    try:
                        total_size += os.path.getsize(file_path)
                    except (OSError, IOError):
                        continue
                        
            return total_size / (1024 ** 3)  # Convert to GB
            
        except Exception as e:
            self.logger.error(f"Error calculating storage usage: {e}")
            return 0.0
            
    def cleanup_database(self, db_path: str):
        """Clean up old database records"""
        with self.cleanup_lock:
            try:
                conn = sqlite3.connect(db_path)
                cursor = conn.cursor()
                
                # Calculate cutoff dates
                results_cutoff = datetime.now() - timedelta(days=self.policy.max_test_results_age_days)
                
                self.logger.info(f"Cleaning database records older than {results_cutoff}")
                
                # Archive old test results before deletion
                if self.policy.enable_archival:
                    self._archive_test_results(conn, results_cutoff)
                
                # Delete old test results
                cursor.execute("""
                    DELETE FROM test_results 
                    WHERE start_time < ?
                """, (results_cutoff,))
                deleted_results = cursor.rowcount
                
                # Delete orphaned coverage metrics
                cursor.execute("""
                    DELETE FROM coverage_metrics 
                    WHERE result_id NOT IN (SELECT result_id FROM test_results)
                """)
                deleted_coverage = cursor.rowcount
                
                # Delete orphaned performance benchmarks
                cursor.execute("""
                    DELETE FROM performance_benchmarks 
                    WHERE result_id NOT IN (SELECT result_id FROM test_results)
                """)
                deleted_perf = cursor.rowcount
                
                # Delete old regression runs
                cursor.execute("""
                    DELETE FROM regression_runs 
                    WHERE start_time < ?
                """, (results_cutoff,))
                deleted_regressions = cursor.rowcount
                
                # Limit total number of test results (keep most recent)
                cursor.execute("""
                    DELETE FROM test_results 
                    WHERE result_id NOT IN (
                        SELECT result_id FROM test_results 
                        ORDER BY start_time DESC 
                        LIMIT ?
                    )
                """, (self.policy.max_test_results_count,))
                deleted_by_count = cursor.rowcount
                
                # Vacuum database to reclaim space
                cursor.execute("VACUUM")
                
                conn.commit()
                conn.close()
                
                self.logger.info(f"Database cleanup completed: "
                               f"Results: {deleted_results}, "
                               f"Coverage: {deleted_coverage}, "
                               f"Performance: {deleted_perf}, "
                               f"Regressions: {deleted_regressions}, "
                               f"Count limit: {deleted_by_count}")
                
            except Exception as e:
                self.logger.error(f"Database cleanup failed: {e}")
                
    def _archive_test_results(self, conn: sqlite3.Connection, cutoff_date: datetime):
        """Archive old test results to compressed files"""
        try:
            cursor = conn.cursor()
            
            # Get test results to archive
            cursor.execute("""
                SELECT tr.*, te.test_id, te.config_id, tc.test_name, tc.category
                FROM test_results tr
                JOIN test_executions te ON tr.execution_id = te.execution_id
                JOIN test_cases tc ON te.test_id = tc.test_id
                WHERE tr.start_time < ?
            """, (cutoff_date,))
            
            results_to_archive = cursor.fetchall()
            
            if not results_to_archive:
                return
                
            # Create archive file
            archive_date = cutoff_date.strftime("%Y%m%d")
            archive_file = self.archive_dir / f"test_results_{archive_date}.json.gz"
            
            # Convert to JSON-serializable format
            archive_data = []
            for row in results_to_archive:
                record = dict(zip([col[0] for col in cursor.description], row))
                # Convert datetime objects to strings
                for key, value in record.items():
                    if isinstance(value, datetime):
                        record[key] = value.isoformat()
                archive_data.append(record)
                
            # Compress and save
            if self.policy.compress_archived:
                with gzip.open(archive_file, 'wt', encoding='utf-8') as f:
                    json.dump(archive_data, f, indent=2)
            else:
                with open(archive_file.with_suffix('.json'), 'w') as f:
                    json.dump(archive_data, f, indent=2)
                    
            self.logger.info(f"Archived {len(archive_data)} test results to {archive_file}")
            
        except Exception as e:
            self.logger.error(f"Archival failed: {e}")
            
    def cleanup_test_workspaces(self):
        """Clean up old test workspaces"""
        with self.cleanup_lock:
            try:
                cutoff_time = time.time() - (self.policy.max_workspace_age_days * 24 * 3600)
                cleaned_count = 0
                cleaned_size = 0
                
                for item in self.base_work_dir.iterdir():
                    if not item.is_dir() or item.name in ['archive', 'reports', 'plots']:
                        continue
                        
                    # Check if this looks like a test workspace
                    if item.name.startswith('test_') and '_' in item.name:
                        # Check modification time
                        if item.stat().st_mtime < cutoff_time:
                            # Calculate size before deletion
                            dir_size = self._get_directory_size(item)
                            
                            # Archive logs if policy allows
                            if self.policy.enable_archival:
                                self._archive_test_workspace(item)
                                
                            # Remove directory
                            shutil.rmtree(item, ignore_errors=True)
                            cleaned_count += 1
                            cleaned_size += dir_size
                            
                self.logger.info(f"Cleaned {cleaned_count} old workspaces, "
                               f"freed {cleaned_size / (1024**2):.1f} MB")
                
            except Exception as e:
                self.logger.error(f"Workspace cleanup failed: {e}")
                
    def _archive_test_workspace(self, workspace_dir: Path):
        """Archive important files from test workspace before deletion"""
        try:
            logs_dir = workspace_dir / "logs"
            if not logs_dir.exists():
                return
                
            # Create archive for this workspace
            archive_name = f"workspace_{workspace_dir.name}.tar.gz"
            archive_path = self.archive_dir / archive_name
            
            # Archive only logs and coverage files
            import tarfile
            with tarfile.open(archive_path, 'w:gz') as tar:
                for log_file in logs_dir.glob('*.log'):
                    tar.add(log_file, arcname=f"logs/{log_file.name}")
                    
                coverage_dir = workspace_dir / "coverage"
                if coverage_dir.exists():
                    for cov_file in coverage_dir.glob('*'):
                        if cov_file.stat().st_size < 10 * 1024 * 1024:  # Only small files
                            tar.add(cov_file, arcname=f"coverage/{cov_file.name}")
                            
            self.logger.debug(f"Archived workspace {workspace_dir.name}")
            
        except Exception as e:
            self.logger.warning(f"Failed to archive workspace {workspace_dir}: {e}")
            
    def cleanup_reports_and_plots(self):
        """Clean up old reports and plots"""
        with self.cleanup_lock:
            try:
                reports_dir = self.base_work_dir / "reports"
                plots_dir = self.base_work_dir / "plots"
                
                cutoff_time = time.time() - (self.policy.max_report_age_days * 24 * 3600)
                plot_cutoff_time = time.time() - (self.policy.max_plot_age_days * 24 * 3600)
                
                # Clean reports
                if reports_dir.exists():
                    cleaned_reports = self._clean_directory_by_age(reports_dir, cutoff_time)
                    self.logger.info(f"Cleaned {cleaned_reports} old reports")
                    
                # Clean plots
                if plots_dir.exists():
                    cleaned_plots = self._clean_directory_by_age(plots_dir, plot_cutoff_time)
                    self.logger.info(f"Cleaned {cleaned_plots} old plots")
                    
            except Exception as e:
                self.logger.error(f"Reports/plots cleanup failed: {e}")
                
    def _clean_directory_by_age(self, directory: Path, cutoff_time: float) -> int:
        """Clean files in directory older than cutoff time"""
        cleaned_count = 0
        
        try:
            for item in directory.iterdir():
                if item.stat().st_mtime < cutoff_time:
                    if item.is_file():
                        item.unlink()
                        cleaned_count += 1
                    elif item.is_dir():
                        shutil.rmtree(item, ignore_errors=True)
                        cleaned_count += 1
                        
        except Exception as e:
            self.logger.warning(f"Error cleaning directory {directory}: {e}")
            
        return cleaned_count
        
    def _get_directory_size(self, directory: Path) -> int:
        """Get total size of directory in bytes"""
        total_size = 0
        try:
            for dirpath, dirnames, filenames in os.walk(directory):
                for filename in filenames:
                    filepath = os.path.join(dirpath, filename)
                    try:
                        total_size += os.path.getsize(filepath)
                    except (OSError, IOError):
                        continue
        except Exception:
            pass
            
        return total_size
        
    def cleanup_old_data(self):
        """Perform comprehensive cleanup of old data"""
        self.logger.info("Starting comprehensive cleanup")
        
        # Clean database
        db_path = self.base_work_dir / "vip_test_config.db"
        if db_path.exists():
            self.cleanup_database(str(db_path))
            
        # Clean workspaces
        self.cleanup_test_workspaces()
        
        # Clean reports and plots
        self.cleanup_reports_and_plots()
        
        # Clean old archives
        self.cleanup_old_archives()
        
        self.logger.info("Comprehensive cleanup completed")
        
    def cleanup_old_archives(self):
        """Clean up very old archive files"""
        try:
            archive_cutoff = time.time() - (self.policy.max_test_results_age_days * 2 * 24 * 3600)
            cleaned_archives = self._clean_directory_by_age(self.archive_dir, archive_cutoff)
            
            if cleaned_archives > 0:
                self.logger.info(f"Cleaned {cleaned_archives} old archive files")
                
        except Exception as e:
            self.logger.error(f"Archive cleanup failed: {e}")
            
    def emergency_cleanup(self):
        """Perform aggressive cleanup when storage is critically low"""
        self.logger.warning("Performing emergency storage cleanup")
        
        with self.cleanup_lock:
            try:
                # More aggressive database cleanup
                db_path = self.base_work_dir / "vip_test_config.db"
                if db_path.exists():
                    conn = sqlite3.connect(str(db_path))
                    cursor = conn.cursor()
                    
                    # Keep only last 30 days and max 5000 results
                    emergency_cutoff = datetime.now() - timedelta(days=30)
                    
                    cursor.execute("""
                        DELETE FROM test_results 
                        WHERE start_time < ? OR result_id NOT IN (
                            SELECT result_id FROM test_results 
                            ORDER BY start_time DESC 
                            LIMIT 5000
                        )
                    """, (emergency_cutoff,))
                    
                    # Clean orphaned records
                    cursor.execute("DELETE FROM coverage_metrics WHERE result_id NOT IN (SELECT result_id FROM test_results)")
                    cursor.execute("DELETE FROM performance_benchmarks WHERE result_id NOT IN (SELECT result_id FROM test_results)")
                    cursor.execute("VACUUM")
                    
                    conn.commit()
                    conn.close()
                    
                # Aggressive workspace cleanup (keep only last 2 days)
                emergency_workspace_cutoff = time.time() - (2 * 24 * 3600)
                for item in self.base_work_dir.iterdir():
                    if (item.is_dir() and item.name.startswith('test_') and 
                        item.stat().st_mtime < emergency_workspace_cutoff):
                        shutil.rmtree(item, ignore_errors=True)
                        
                # Clean all reports older than 7 days
                reports_dir = self.base_work_dir / "reports"
                if reports_dir.exists():
                    report_cutoff = time.time() - (7 * 24 * 3600)
                    self._clean_directory_by_age(reports_dir, report_cutoff)
                    
                # Clean all plots older than 3 days
                plots_dir = self.base_work_dir / "plots"
                if plots_dir.exists():
                    plot_cutoff = time.time() - (3 * 24 * 3600)
                    self._clean_directory_by_age(plots_dir, plot_cutoff)
                    
                self.logger.warning("Emergency cleanup completed")
                
            except Exception as e:
                self.logger.error(f"Emergency cleanup failed: {e}")
                
    def limit_log_file_size(self, log_file_path: str):
        """Limit log file size and rotate if necessary"""
        try:
            log_path = Path(log_file_path)
            if not log_path.exists():
                return
                
            max_size = self.policy.max_log_file_size_mb * 1024 * 1024
            current_size = log_path.stat().st_size
            
            if current_size > max_size:
                # Rotate log file
                backup_path = log_path.with_suffix('.log.old')
                
                # Keep only the last part of the log
                with open(log_path, 'r') as f:
                    lines = f.readlines()
                    
                # Keep last 50% of lines
                keep_lines = lines[len(lines)//2:]
                
                # Move current to backup
                if backup_path.exists():
                    backup_path.unlink()
                log_path.rename(backup_path)
                
                # Write truncated version
                with open(log_path, 'w') as f:
                    f.write("... [Log truncated due to size limit] ...\n")
                    f.writelines(keep_lines)
                    
                self.logger.info(f"Rotated log file {log_file_path} (was {current_size/1024/1024:.1f} MB)")
                
        except Exception as e:
            self.logger.warning(f"Failed to rotate log file {log_file_path}: {e}")
            
    def get_storage_stats(self) -> Dict[str, Any]:
        """Get comprehensive storage statistics"""
        try:
            stats = {
                'total_usage_gb': self.get_total_storage_usage(),
                'policy_limits': {
                    'max_total_gb': self.policy.max_total_storage_gb,
                    'emergency_threshold_gb': self.policy.emergency_cleanup_threshold_gb
                }
            }
            
            # Database stats
            db_path = self.base_work_dir / "vip_test_config.db"
            if db_path.exists():
                stats['database_size_mb'] = db_path.stat().st_size / (1024 ** 2)
                
            # Workspace stats
            workspace_count = 0
            workspace_size = 0
            for item in self.base_work_dir.iterdir():
                if item.is_dir() and item.name.startswith('test_'):
                    workspace_count += 1
                    workspace_size += self._get_directory_size(item)
                    
            stats['workspaces'] = {
                'count': workspace_count,
                'total_size_mb': workspace_size / (1024 ** 2)
            }
            
            # Archive stats
            archive_count = 0
            archive_size = 0
            if self.archive_dir.exists():
                for item in self.archive_dir.iterdir():
                    if item.is_file():
                        archive_count += 1
                        archive_size += item.stat().st_size
                        
            stats['archives'] = {
                'count': archive_count,
                'total_size_mb': archive_size / (1024 ** 2)
            }
            
            return stats
            
        except Exception as e:
            self.logger.error(f"Failed to get storage stats: {e}")
            return {'error': str(e)}
            
    def shutdown(self):
        """Shutdown storage manager"""
        self.logger.info("Shutting down storage manager")
        self.shutdown_event.set()
        
        if self.cleanup_thread and self.cleanup_thread.is_alive():
            self.cleanup_thread.join(timeout=10)
            
    def __enter__(self):
        return self
        
    def __exit__(self, exc_type, exc_val, exc_tb):
        self.shutdown()

# Singleton instance for global use
_storage_manager_instance = None

def get_storage_manager(base_work_dir: str = "/tmp/vip_test_runs", 
                       policy: StoragePolicy = None) -> VIPStorageManager:
    """Get singleton storage manager instance"""
    global _storage_manager_instance
    
    if _storage_manager_instance is None:
        _storage_manager_instance = VIPStorageManager(base_work_dir, policy)
        
    return _storage_manager_instance

def example_usage():
    """Example of using the storage manager"""
    
    # Create custom storage policy
    policy = StoragePolicy(
        max_test_results_age_days=60,
        max_workspace_age_days=5,
        max_total_storage_gb=20,
        cleanup_interval_hours=2
    )
    
    # Initialize storage manager
    storage_manager = VIPStorageManager(policy=policy)
    
    try:
        # Get current stats
        stats = storage_manager.get_storage_stats()
        print(f"Current storage usage: {stats['total_usage_gb']:.2f} GB")
        
        # Perform cleanup
        storage_manager.cleanup_old_data()
        
        # Get updated stats
        stats = storage_manager.get_storage_stats()
        print(f"Storage usage after cleanup: {stats['total_usage_gb']:.2f} GB")
        
    finally:
        storage_manager.shutdown()

if __name__ == "__main__":
    example_usage()