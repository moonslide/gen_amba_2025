#!/usr/bin/env python3

"""
AXI4 VIP Regression Management and Scheduling System
Comprehensive regression management with intelligent scheduling, resource allocation, 
and adaptive test selection based on tim_axi4_vip architecture.
"""

import os
import sys
import time
import json
import threading
import schedule
import sqlite3
from datetime import datetime, timedelta
from typing import Dict, List, Any, Optional, Tuple, Set
from dataclasses import dataclass, asdict
from enum import Enum
import subprocess
import logging
from pathlib import Path
import concurrent.futures
from collections import defaultdict
import statistics
import heapq

from test_config_manager import VIPTestConfigManager
from vip_test_execution_framework import VIPTestExecutionFramework, TestExecution, TestStatus

class RegressionType(Enum):
    """Types of regression runs"""
    SMOKE = "smoke"
    SANITY = "sanity"
    FULL = "full"
    STRESS = "stress"
    NIGHTLY = "nightly"
    WEEKLY = "weekly"
    RELEASE = "release"
    CUSTOM = "custom"

class ScheduleType(Enum):
    """Schedule types for regression runs"""
    IMMEDIATE = "immediate"
    SCHEDULED = "scheduled"
    TRIGGERED = "triggered"
    CONTINUOUS = "continuous"

@dataclass
class RegressionConfig:
    """Configuration for a regression run"""
    name: str
    suite_id: int
    config_id: int
    regression_type: RegressionType
    schedule_type: ScheduleType
    priority: int = 3  # 1=highest, 5=lowest
    max_parallel_tests: int = 4
    timeout_hours: int = 8
    retry_failed: bool = True
    max_retries: int = 2
    stop_on_fail_threshold: int = 10  # Stop if more than N tests fail
    coverage_threshold: float = 80.0  # Minimum coverage percentage
    test_filters: Dict[str, Any] = None
    notification_emails: List[str] = None
    git_commit_hash: str = ""
    git_branch: str = ""
    environment_vars: Dict[str, str] = None
    
    def __post_init__(self):
        if self.test_filters is None:
            self.test_filters = {}
        if self.notification_emails is None:
            self.notification_emails = []
        if self.environment_vars is None:
            self.environment_vars = {}

@dataclass
class RegressionRun:
    """Active regression run state"""
    regression_id: int
    config: RegressionConfig
    start_time: datetime
    status: str = "RUNNING"
    completed_tests: int = 0
    passed_tests: int = 0
    failed_tests: int = 0
    skipped_tests: int = 0
    total_tests: int = 0
    current_coverage: float = 0.0
    estimated_completion: Optional[datetime] = None
    test_executions: List[TestExecution] = None
    
    def __post_init__(self):
        if self.test_executions is None:
            self.test_executions = []

class VIPRegressionManager:
    """Comprehensive regression management and scheduling system"""
    
    def __init__(self, db_manager: VIPTestConfigManager, 
                 execution_framework: VIPTestExecutionFramework):
        self.db_manager = db_manager
        self.execution_framework = execution_framework
        self.active_regressions: Dict[int, RegressionRun] = {}
        self.scheduled_regressions: List[Tuple[datetime, RegressionConfig]] = []
        self.scheduler_thread = None
        self.shutdown_event = threading.Event()
        
        # Setup logging
        self.logger = self._setup_logging()
        
        # Resource management
        self.max_concurrent_regressions = 2
        self.resource_lock = threading.Lock()
        
        # Statistics tracking
        self.regression_stats = defaultdict(list)
        
        # Initialize scheduler
        self._init_scheduler()
        
        # Register callbacks
        self.execution_framework.add_result_callback(self._on_test_completion)
        
    def _setup_logging(self) -> logging.Logger:
        """Setup logging for regression manager"""
        logger = logging.getLogger('VIPRegressionManager')
        logger.setLevel(logging.INFO)
        
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            
        return logger
        
    def _init_scheduler(self):
        """Initialize the regression scheduler"""
        # Schedule common regression types
        schedule.every().day.at("02:00").do(self._run_nightly_regression)
        schedule.every().sunday.at("01:00").do(self._run_weekly_regression)
        
        # Start scheduler thread
        self.scheduler_thread = threading.Thread(target=self._scheduler_loop, daemon=True)
        self.scheduler_thread.start()
        
    def _scheduler_loop(self):
        """Main scheduler loop"""
        self.logger.info("Regression scheduler started")
        
        while not self.shutdown_event.is_set():
            try:
                # Run scheduled jobs
                schedule.run_pending()
                
                # Check for immediate regressions
                self._process_immediate_regressions()
                
                # Update active regressions
                self._update_active_regressions()
                
                time.sleep(30)  # Check every 30 seconds
                
            except Exception as e:
                self.logger.error(f"Error in scheduler loop: {e}")
                
        self.logger.info("Regression scheduler stopped")
        
    def create_regression_config(self, name: str, suite_id: int, config_id: int,
                                regression_type: RegressionType = RegressionType.FULL,
                                **kwargs) -> RegressionConfig:
        """Create a new regression configuration"""
        config = RegressionConfig(
            name=name,
            suite_id=suite_id,
            config_id=config_id,
            regression_type=regression_type,
            schedule_type=ScheduleType.IMMEDIATE,
            **kwargs
        )
        
        self.logger.info(f"Created regression config: {name}")
        return config
        
    def schedule_regression(self, config: RegressionConfig, 
                          schedule_time: Optional[datetime] = None) -> int:
        """Schedule a regression run"""
        
        if schedule_time is None:
            schedule_time = datetime.now()
            
        # Create regression run record in database
        regression_id = self.db_manager.create_regression_run(
            name=config.name,
            suite_id=config.suite_id,
            config_id=config.config_id,
            trigger_type=config.schedule_type.value,
            git_commit_hash=config.git_commit_hash,
            git_branch=config.git_branch,
            comments=f"Regression type: {config.regression_type.value}"
        )
        
        if config.schedule_type == ScheduleType.IMMEDIATE:
            # Start immediately
            self._start_regression(regression_id, config)
        else:
            # Add to scheduled list
            self.scheduled_regressions.append((schedule_time, config))
            self.scheduled_regressions.sort(key=lambda x: x[0])
            
        self.logger.info(f"Scheduled regression {config.name} with ID {regression_id}")
        return regression_id
        
    def _start_regression(self, regression_id: int, config: RegressionConfig) -> bool:
        """Start executing a regression run"""
        
        with self.resource_lock:
            if len(self.active_regressions) >= self.max_concurrent_regressions:
                self.logger.warning(f"Maximum concurrent regressions reached, queuing {config.name}")
                return False
                
        try:
            # Get test cases for the regression
            test_cases = self._select_tests_for_regression(config)
            
            if not test_cases:
                self.logger.error(f"No test cases found for regression {config.name}")
                return False
                
            # Create regression run
            regression_run = RegressionRun(
                regression_id=regression_id,
                config=config,
                start_time=datetime.now(),
                total_tests=len(test_cases)
            )
            
            # Generate test executions
            test_executions = self._create_test_executions(test_cases, config)
            regression_run.test_executions = test_executions
            
            # Estimate completion time
            regression_run.estimated_completion = self._estimate_completion_time(test_executions)
            
            # Add to active regressions
            self.active_regressions[regression_id] = regression_run
            
            # Submit tests to execution framework
            self._submit_regression_tests(regression_run)
            
            self.logger.info(f"Started regression {config.name} with {len(test_cases)} tests")
            return True
            
        except Exception as e:
            self.logger.error(f"Failed to start regression {config.name}: {e}")
            return False
            
    def _select_tests_for_regression(self, config: RegressionConfig) -> List[Dict]:
        """Select test cases based on regression configuration"""
        
        # Get all test cases in the suite
        all_tests = self.db_manager.get_test_cases(suite_id=config.suite_id)
        
        # Apply regression type filtering
        if config.regression_type == RegressionType.SMOKE:
            # Only priority 1 tests
            selected_tests = [t for t in all_tests if t['priority'] == 1]
        elif config.regression_type == RegressionType.SANITY:
            # Priority 1 and 2 tests
            selected_tests = [t for t in all_tests if t['priority'] <= 2]
        elif config.regression_type == RegressionType.STRESS:
            # Only stress tests
            selected_tests = [t for t in all_tests if t['test_type'] == 'stress']
        elif config.regression_type == RegressionType.FULL:
            # All enabled tests
            selected_tests = all_tests
        else:
            # Custom filtering based on test_filters
            selected_tests = self._apply_custom_filters(all_tests, config.test_filters)
            
        # Apply additional filters
        if config.test_filters:
            selected_tests = self._apply_custom_filters(selected_tests, config.test_filters)
            
        # Smart test selection based on history
        if config.regression_type in [RegressionType.NIGHTLY, RegressionType.WEEKLY]:
            selected_tests = self._apply_smart_selection(selected_tests, config)
            
        self.logger.info(f"Selected {len(selected_tests)} tests for {config.regression_type.value} regression")
        return selected_tests
        
    def _apply_custom_filters(self, tests: List[Dict], filters: Dict[str, Any]) -> List[Dict]:
        """Apply custom test filters"""
        filtered_tests = tests
        
        for filter_key, filter_value in filters.items():
            if filter_key == 'categories':
                if isinstance(filter_value, list):
                    filtered_tests = [t for t in filtered_tests if t['category'] in filter_value]
                else:
                    filtered_tests = [t for t in filtered_tests if t['category'] == filter_value]
            elif filter_key == 'test_types':
                if isinstance(filter_value, list):
                    filtered_tests = [t for t in filtered_tests if t['test_type'] in filter_value]
                else:
                    filtered_tests = [t for t in filtered_tests if t['test_type'] == filter_value]
            elif filter_key == 'max_priority':
                filtered_tests = [t for t in filtered_tests if t['priority'] <= filter_value]
            elif filter_key == 'exclude_categories':
                if isinstance(filter_value, list):
                    filtered_tests = [t for t in filtered_tests if t['category'] not in filter_value]
                else:
                    filtered_tests = [t for t in filtered_tests if t['category'] != filter_value]
                    
        return filtered_tests
        
    def _apply_smart_selection(self, tests: List[Dict], config: RegressionConfig) -> List[Dict]:
        """Apply smart test selection based on historical data"""
        
        # Get test history and failure rates
        test_scores = {}
        
        for test in tests:
            test_id = test['test_id']
            
            # Get recent results for this test
            recent_results = self._get_recent_test_results(test_id, days=30)
            
            if not recent_results:
                # New test - include it
                test_scores[test_id] = 1.0
                continue
                
            # Calculate failure rate
            total_runs = len(recent_results)
            failures = sum(1 for r in recent_results if r['status'] in ['FAIL', 'ERROR', 'TIMEOUT'])
            failure_rate = failures / total_runs if total_runs > 0 else 0
            
            # Calculate coverage contribution
            avg_coverage = statistics.mean([r['coverage_percentage'] for r in recent_results if r['coverage_percentage'] > 0])
            coverage_score = avg_coverage / 100.0 if avg_coverage > 0 else 0.5
            
            # Calculate execution time score (prefer faster tests for frequent runs)
            avg_duration = statistics.mean([r['duration_seconds'] for r in recent_results if r['duration_seconds'] > 0])
            time_score = max(0.1, 1.0 - (avg_duration / 3600))  # Normalize to 1 hour
            
            # Combined score
            score = (failure_rate * 0.4) + (coverage_score * 0.4) + (time_score * 0.2)
            test_scores[test_id] = score
            
        # Sort tests by score and select top tests if needed
        if config.regression_type == RegressionType.NIGHTLY:
            # Select top 80% of tests by score for nightly runs
            sorted_tests = sorted(tests, key=lambda t: test_scores.get(t['test_id'], 0.5), reverse=True)
            selected_count = int(len(sorted_tests) * 0.8)
            return sorted_tests[:selected_count]
        else:
            return tests
            
    def _get_recent_test_results(self, test_id: int, days: int = 30) -> List[Dict]:
        """Get recent test results for analysis"""
        cursor = self.db_manager.conn.cursor()
        cursor.execute("""
            SELECT tr.status, tr.duration_seconds, tr.coverage_percentage, tr.start_time
            FROM test_results tr
            JOIN test_executions te ON tr.execution_id = te.execution_id
            WHERE te.test_id = ? 
              AND tr.start_time >= datetime('now', '-{} days')
            ORDER BY tr.start_time DESC
        """.format(days), (test_id,))
        
        return [dict(row) for row in cursor.fetchall()]
        
    def _create_test_executions(self, test_cases: List[Dict], 
                              config: RegressionConfig) -> List[TestExecution]:
        """Create test execution configurations"""
        
        test_executions = []
        
        for i, test_case in enumerate(test_cases):
            # Create execution configuration
            execution_id = int(f"{config.suite_id}{config.config_id}{i:04d}")
            
            test_execution = TestExecution(
                execution_id=execution_id,
                test_name=test_case['test_name'],
                test_id=test_case['test_id'],
                config_id=config.config_id,
                simulator="questa",  # Default simulator
                compile_args="-O2 +acc",
                simulation_args=f"+UVM_TESTNAME={test_case['test_name'].lower().replace(' ', '_')}",
                seed=self._generate_seed(test_case['test_id'], config),
                timeout_seconds=test_case.get('timeout_seconds', 3600),
                work_dir="",  # Will be set by execution framework
                log_file=""   # Will be set by execution framework
            )
            
            test_executions.append(test_execution)
            
        return test_executions
        
    def _generate_seed(self, test_id: int, config: RegressionConfig) -> int:
        """Generate deterministic but varied seeds for tests"""
        base_seed = hash(f"{config.git_commit_hash}_{test_id}") % (2**31)
        return abs(base_seed)
        
    def _estimate_completion_time(self, test_executions: List[TestExecution]) -> datetime:
        """Estimate regression completion time"""
        
        total_estimated_time = 0
        
        for test_execution in test_executions:
            # Get historical average runtime for this test
            avg_runtime = self._get_average_test_runtime(test_execution.test_id)
            if avg_runtime:
                estimated_time = avg_runtime * 1.2  # Add 20% buffer
            else:
                estimated_time = test_execution.timeout_seconds * 0.5  # Assume 50% of timeout
                
            total_estimated_time += estimated_time
            
        # Account for parallelism
        parallel_time = total_estimated_time / min(len(test_executions), 
                                                 self.execution_framework.max_concurrent_tests)
        
        return datetime.now() + timedelta(seconds=parallel_time)
        
    def _get_average_test_runtime(self, test_id: int) -> Optional[float]:
        """Get average runtime for a test from historical data"""
        cursor = self.db_manager.conn.cursor()
        cursor.execute("""
            SELECT AVG(tr.duration_seconds) as avg_duration
            FROM test_results tr
            JOIN test_executions te ON tr.execution_id = te.execution_id
            WHERE te.test_id = ? 
              AND tr.status = 'PASS'
              AND tr.start_time >= datetime('now', '-90 days')
        """, (test_id,))
        
        result = cursor.fetchone()
        return result['avg_duration'] if result and result['avg_duration'] else None
        
    def _submit_regression_tests(self, regression_run: RegressionRun):
        """Submit regression tests to execution framework"""
        
        # Priority-based submission
        prioritized_tests = sorted(
            regression_run.test_executions,
            key=lambda t: self._get_test_priority_score(t, regression_run.config)
        )
        
        for test_execution in prioritized_tests:
            self.execution_framework.submit_test(test_execution)
            
    def _get_test_priority_score(self, test_execution: TestExecution, 
                               config: RegressionConfig) -> float:
        """Calculate priority score for test ordering"""
        
        # Get test info from database
        cursor = self.db_manager.conn.cursor()
        cursor.execute("SELECT priority, category FROM test_cases WHERE test_id = ?", 
                      (test_execution.test_id,))
        test_info = cursor.fetchone()
        
        if not test_info:
            return 5.0  # Lowest priority
            
        priority = test_info['priority']
        category = test_info['category']
        
        # Base score from test priority
        score = priority
        
        # Adjust based on category importance
        category_weights = {
            'basic': 1.0,
            'protocol': 1.2,
            'burst': 1.1,
            'exclusive': 1.3,
            'qos': 1.4,
            'error': 1.2,
            'performance': 1.5,
            'stress': 2.0
        }
        
        weight = category_weights.get(category, 1.0)
        score /= weight
        
        # Prioritize recently failing tests
        recent_failures = self._count_recent_failures(test_execution.test_id, days=7)
        if recent_failures > 0:
            score *= 0.8  # Higher priority (lower score)
            
        return score
        
    def _count_recent_failures(self, test_id: int, days: int = 7) -> int:
        """Count recent failures for a test"""
        cursor = self.db_manager.conn.cursor()
        cursor.execute("""
            SELECT COUNT(*) as failure_count
            FROM test_results tr
            JOIN test_executions te ON tr.execution_id = te.execution_id
            WHERE te.test_id = ? 
              AND tr.status IN ('FAIL', 'ERROR', 'TIMEOUT')
              AND tr.start_time >= datetime('now', '-{} days')
        """.format(days), (test_id,))
        
        result = cursor.fetchone()
        return result['failure_count'] if result else 0
        
    def _on_test_completion(self, test_execution: TestExecution):
        """Handle test completion in regression context"""
        
        # Find which regression this test belongs to
        regression_run = None
        for reg_run in self.active_regressions.values():
            for reg_test in reg_run.test_executions:
                if reg_test.execution_id == test_execution.execution_id:
                    regression_run = reg_run
                    break
            if regression_run:
                break
                
        if not regression_run:
            return  # Test not part of any active regression
            
        # Update regression statistics
        regression_run.completed_tests += 1
        
        if test_execution.status == TestStatus.COMPLETED:
            regression_run.passed_tests += 1
        elif test_execution.status in [TestStatus.FAILED, TestStatus.ERROR, TestStatus.TIMEOUT]:
            regression_run.failed_tests += 1
            
            # Check if we should retry the test
            if (regression_run.config.retry_failed and 
                hasattr(test_execution, 'retry_count') and 
                test_execution.retry_count < regression_run.config.max_retries):
                
                self._retry_failed_test(test_execution, regression_run)
        else:
            regression_run.skipped_tests += 1
            
        # Update coverage
        if test_execution.coverage_percentage > 0:
            total_coverage = (regression_run.current_coverage * (regression_run.completed_tests - 1) + 
                            test_execution.coverage_percentage) / regression_run.completed_tests
            regression_run.current_coverage = total_coverage
            
        # Check stopping conditions
        self._check_regression_stopping_conditions(regression_run)
        
        # Update database
        self._update_regression_database(regression_run)
        
    def _retry_failed_test(self, test_execution: TestExecution, regression_run: RegressionRun):
        """Retry a failed test"""
        
        # Create new execution with incremented retry count
        retry_execution = TestExecution(
            execution_id=test_execution.execution_id + 100000,  # Different ID for retry
            test_name=f"{test_execution.test_name} (Retry)",
            test_id=test_execution.test_id,
            config_id=test_execution.config_id,
            simulator=test_execution.simulator,
            compile_args=test_execution.compile_args,
            simulation_args=test_execution.simulation_args,
            seed=test_execution.seed + 1,  # Different seed
            timeout_seconds=test_execution.timeout_seconds,
            work_dir="",
            log_file=""
        )
        
        setattr(retry_execution, 'retry_count', getattr(test_execution, 'retry_count', 0) + 1)
        
        # Add to regression and submit
        regression_run.test_executions.append(retry_execution)
        regression_run.total_tests += 1
        
        self.execution_framework.submit_test(retry_execution)
        
        self.logger.info(f"Retrying failed test: {test_execution.test_name}")
        
    def _check_regression_stopping_conditions(self, regression_run: RegressionRun):
        """Check if regression should be stopped early"""
        
        config = regression_run.config
        
        # Check failure threshold
        if regression_run.failed_tests > config.stop_on_fail_threshold:
            self._stop_regression(regression_run, "Too many test failures")
            return
            
        # Check timeout
        elapsed_time = datetime.now() - regression_run.start_time
        if elapsed_time > timedelta(hours=config.timeout_hours):
            self._stop_regression(regression_run, "Timeout exceeded")
            return
            
        # Check if all tests completed
        if regression_run.completed_tests >= regression_run.total_tests:
            self._complete_regression(regression_run)
            
    def _stop_regression(self, regression_run: RegressionRun, reason: str):
        """Stop a regression run"""
        
        regression_run.status = "STOPPED"
        
        # Abort remaining tests
        for test_execution in regression_run.test_executions:
            if test_execution.status in [TestStatus.PENDING, TestStatus.QUEUED, TestStatus.RUNNING]:
                self.execution_framework.abort_test(test_execution.execution_id)
                
        self.logger.warning(f"Stopped regression {regression_run.config.name}: {reason}")
        
        # Update database
        self._update_regression_database(regression_run)
        
        # Send notifications
        self._send_regression_notifications(regression_run, f"Stopped: {reason}")
        
        # Remove from active regressions
        del self.active_regressions[regression_run.regression_id]
        
    def _complete_regression(self, regression_run: RegressionRun):
        """Complete a regression run"""
        
        regression_run.status = "COMPLETED"
        
        # Calculate final statistics
        pass_rate = (regression_run.passed_tests / regression_run.total_tests * 100 
                    if regression_run.total_tests > 0 else 0)
        
        self.logger.info(f"Completed regression {regression_run.config.name}: "
                        f"{regression_run.passed_tests}/{regression_run.total_tests} passed "
                        f"({pass_rate:.1f}%), Coverage: {regression_run.current_coverage:.1f}%")
        
        # Update database
        self._update_regression_database(regression_run)
        
        # Generate report
        self._generate_regression_report(regression_run)
        
        # Send notifications
        self._send_regression_notifications(regression_run, "Completed")
        
        # Clean up
        self._cleanup_regression(regression_run)
        
        # Remove from active regressions
        del self.active_regressions[regression_run.regression_id]
        
    def _update_regression_database(self, regression_run: RegressionRun):
        """Update regression run in database"""
        
        self.db_manager.update_regression_stats(
            regression_run.regression_id,
            regression_run.total_tests,
            regression_run.passed_tests,
            regression_run.failed_tests,
            regression_run.skipped_tests,
            regression_run.current_coverage
        )
        
    def _generate_regression_report(self, regression_run: RegressionRun):
        """Generate comprehensive regression report"""
        
        report_dir = Path(f"/tmp/regression_reports/{regression_run.regression_id}")
        report_dir.mkdir(parents=True, exist_ok=True)
        
        # HTML Report
        html_report = self._generate_html_report(regression_run)
        with open(report_dir / "report.html", 'w') as f:
            f.write(html_report)
            
        # JSON Summary
        json_summary = self._generate_json_summary(regression_run)
        with open(report_dir / "summary.json", 'w') as f:
            json.dump(json_summary, f, indent=2, default=str)
            
        self.logger.info(f"Generated regression report in {report_dir}")
        
    def _generate_html_report(self, regression_run: RegressionRun) -> str:
        """Generate HTML regression report"""
        
        # This would generate a comprehensive HTML report
        # For brevity, showing a basic template
        
        html_template = f"""
<!DOCTYPE html>
<html>
<head>
    <title>Regression Report - {regression_run.config.name}</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 20px; }}
        .header {{ background-color: #f0f0f0; padding: 20px; }}
        .summary {{ display: flex; gap: 20px; margin: 20px 0; }}
        .metric {{ background-color: #e8f4f8; padding: 15px; border-radius: 5px; }}
        .pass {{ color: green; }}
        .fail {{ color: red; }}
        table {{ border-collapse: collapse; width: 100%; }}
        th, td {{ border: 1px solid #ddd; padding: 8px; text-align: left; }}
        th {{ background-color: #f2f2f2; }}
    </style>
</head>
<body>
    <div class="header">
        <h1>Regression Report</h1>
        <h2>{regression_run.config.name}</h2>
        <p>Type: {regression_run.config.regression_type.value}</p>
        <p>Started: {regression_run.start_time}</p>
        <p>Status: {regression_run.status}</p>
    </div>
    
    <div class="summary">
        <div class="metric">
            <h3>Tests</h3>
            <p>Total: {regression_run.total_tests}</p>
            <p class="pass">Passed: {regression_run.passed_tests}</p>
            <p class="fail">Failed: {regression_run.failed_tests}</p>
            <p>Skipped: {regression_run.skipped_tests}</p>
        </div>
        <div class="metric">
            <h3>Coverage</h3>
            <p>{regression_run.current_coverage:.1f}%</p>
        </div>
        <div class="metric">
            <h3>Pass Rate</h3>
            <p>{regression_run.passed_tests/regression_run.total_tests*100:.1f}%</p>
        </div>
    </div>
    
    <!-- Test details table would go here -->
    
</body>
</html>
        """
        
        return html_template
        
    def _generate_json_summary(self, regression_run: RegressionRun) -> Dict[str, Any]:
        """Generate JSON summary of regression run"""
        
        return {
            'regression_id': regression_run.regression_id,
            'name': regression_run.config.name,
            'type': regression_run.config.regression_type.value,
            'start_time': regression_run.start_time,
            'status': regression_run.status,
            'statistics': {
                'total_tests': regression_run.total_tests,
                'passed_tests': regression_run.passed_tests,
                'failed_tests': regression_run.failed_tests,
                'skipped_tests': regression_run.skipped_tests,
                'pass_rate': regression_run.passed_tests / regression_run.total_tests * 100 if regression_run.total_tests > 0 else 0,
                'coverage': regression_run.current_coverage
            },
            'configuration': asdict(regression_run.config),
            'test_results': [
                {
                    'execution_id': te.execution_id,
                    'test_name': te.test_name,
                    'status': te.status.value if hasattr(te.status, 'value') else str(te.status),
                    'coverage': te.coverage_percentage,
                    'duration': (te.end_time - te.start_time).total_seconds() if te.end_time and te.start_time else 0
                }
                for te in regression_run.test_executions
                if te.status not in [TestStatus.PENDING, TestStatus.QUEUED]
            ]
        }
        
    def _send_regression_notifications(self, regression_run: RegressionRun, event: str):
        """Send regression notifications"""
        
        if not regression_run.config.notification_emails:
            return
            
        subject = f"Regression {event}: {regression_run.config.name}"
        
        pass_rate = (regression_run.passed_tests / regression_run.total_tests * 100 
                    if regression_run.total_tests > 0 else 0)
        
        body = f"""
Regression Run {event}

Name: {regression_run.config.name}
Type: {regression_run.config.regression_type.value}
Status: {regression_run.status}

Results:
- Total Tests: {regression_run.total_tests}
- Passed: {regression_run.passed_tests} ({pass_rate:.1f}%)
- Failed: {regression_run.failed_tests}
- Coverage: {regression_run.current_coverage:.1f}%

Started: {regression_run.start_time}
Duration: {datetime.now() - regression_run.start_time}

Git Branch: {regression_run.config.git_branch}
Git Commit: {regression_run.config.git_commit_hash}
        """
        
        # Send email notifications (implementation would depend on email system)
        self.logger.info(f"Sending notifications for regression {regression_run.config.name}")
        
    def _cleanup_regression(self, regression_run: RegressionRun):
        """Clean up regression artifacts"""
        
        # Clean up test workspaces if configured
        for test_execution in regression_run.test_executions:
            if hasattr(test_execution, 'execution_id'):
                self.execution_framework.cleanup_test_workspace(
                    test_execution.execution_id, 
                    keep_logs=True
                )
                
    def _process_immediate_regressions(self):
        """Process regressions scheduled for immediate execution"""
        
        current_time = datetime.now()
        ready_regressions = []
        
        for schedule_time, config in self.scheduled_regressions:
            if schedule_time <= current_time:
                ready_regressions.append((schedule_time, config))
                
        # Remove processed regressions from schedule
        for item in ready_regressions:
            self.scheduled_regressions.remove(item)
            
            # Start the regression
            regression_id = self.db_manager.create_regression_run(
                name=item[1].name,
                suite_id=item[1].suite_id,
                config_id=item[1].config_id,
                trigger_type=item[1].schedule_type.value
            )
            
            self._start_regression(regression_id, item[1])
            
    def _update_active_regressions(self):
        """Update status of active regressions"""
        
        for regression_run in list(self.active_regressions.values()):
            # Update completion estimates
            if regression_run.estimated_completion:
                remaining_tests = regression_run.total_tests - regression_run.completed_tests
                if remaining_tests > 0 and regression_run.completed_tests > 0:
                    elapsed = datetime.now() - regression_run.start_time
                    avg_time_per_test = elapsed.total_seconds() / regression_run.completed_tests
                    estimated_remaining = timedelta(seconds=avg_time_per_test * remaining_tests)
                    regression_run.estimated_completion = datetime.now() + estimated_remaining
                    
    def _run_nightly_regression(self):
        """Run nightly regression"""
        config = RegressionConfig(
            name=f"Nightly_Regression_{datetime.now().strftime('%Y%m%d')}",
            suite_id=1,  # Default suite
            config_id=1,  # Default config
            regression_type=RegressionType.NIGHTLY,
            schedule_type=ScheduleType.SCHEDULED,
            priority=2,
            max_parallel_tests=8,
            timeout_hours=12
        )
        
        self.schedule_regression(config)
        
    def _run_weekly_regression(self):
        """Run weekly regression"""
        config = RegressionConfig(
            name=f"Weekly_Regression_{datetime.now().strftime('%Y%m%d')}",
            suite_id=1,  # Default suite
            config_id=1,  # Default config
            regression_type=RegressionType.WEEKLY,
            schedule_type=ScheduleType.SCHEDULED,
            priority=3,
            max_parallel_tests=4,
            timeout_hours=24
        )
        
        self.schedule_regression(config)
        
    def get_active_regressions(self) -> List[RegressionRun]:
        """Get list of currently active regressions"""
        return list(self.active_regressions.values())
        
    def get_regression_status(self, regression_id: int) -> Optional[RegressionRun]:
        """Get status of a specific regression"""
        return self.active_regressions.get(regression_id)
        
    def abort_regression(self, regression_id: int) -> bool:
        """Abort a running regression"""
        if regression_id in self.active_regressions:
            regression_run = self.active_regressions[regression_id]
            self._stop_regression(regression_run, "Aborted by user")
            return True
        return False
        
    def shutdown(self):
        """Shutdown the regression manager"""
        self.logger.info("Shutting down regression manager...")
        
        # Signal shutdown
        self.shutdown_event.set()
        
        # Abort all active regressions
        for regression_id in list(self.active_regressions.keys()):
            self.abort_regression(regression_id)
            
        # Wait for scheduler thread
        if self.scheduler_thread:
            self.scheduler_thread.join(timeout=10)
            
        self.logger.info("Regression manager shutdown complete")

# Example usage
def example_regression_management():
    """Example of using the regression manager"""
    
    # Initialize components
    db_manager = VIPTestConfigManager()
    execution_framework = VIPTestExecutionFramework()
    regression_manager = VIPRegressionManager(db_manager, execution_framework)
    
    # Create regression configuration
    config = regression_manager.create_regression_config(
        name="Example_Full_Regression",
        suite_id=1,
        config_id=1,
        regression_type=RegressionType.FULL,
        max_parallel_tests=4,
        coverage_threshold=85.0,
        notification_emails=["engineer@company.com"]
    )
    
    # Schedule regression
    regression_id = regression_manager.schedule_regression(config)
    
    # Monitor progress
    try:
        while True:
            active_regressions = regression_manager.get_active_regressions()
            if not active_regressions:
                break
                
            for regression in active_regressions:
                print(f"Regression {regression.config.name}: "
                      f"{regression.completed_tests}/{regression.total_tests} tests completed")
                      
            time.sleep(10)
            
    except KeyboardInterrupt:
        print("Interrupted - aborting regressions...")
        regression_manager.abort_regression(regression_id)
        
    finally:
        regression_manager.shutdown()
        execution_framework.shutdown()
        db_manager.close()

if __name__ == "__main__":
    example_regression_management()