#!/usr/bin/env python3

"""
AXI4 VIP Test Reporting and Analysis Tools
Comprehensive test reporting system with advanced analytics, visualizations, 
and trend analysis based on tim_axi4_vip architecture.
"""

import os
import sys
import json
import sqlite3
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from datetime import datetime, timedelta
from typing import Dict, List, Any, Optional, Tuple
from pathlib import Path
from dataclasses import dataclass
import logging
from jinja2 import Template
import plotly.graph_objects as go
import plotly.express as px
from plotly.subplots import make_subplots
import plotly.offline as pyo
from io import StringIO
import base64

from test_config_manager import VIPTestConfigManager

@dataclass
class ReportConfig:
    """Configuration for report generation"""
    report_type: str  # summary, detailed, trend, comparison
    time_range_days: int = 30
    include_plots: bool = True
    include_coverage: bool = True
    include_performance: bool = True
    output_format: str = "html"  # html, pdf, json
    output_dir: str = "/tmp/vip_reports"
    test_suites: List[int] = None
    test_categories: List[str] = None
    regression_ids: List[int] = None
    
    def __post_init__(self):
        if self.test_suites is None:
            self.test_suites = []
        if self.test_categories is None:
            self.test_categories = []
        if self.regression_ids is None:
            self.regression_ids = []

class VIPTestReportingAnalyzer:
    """Comprehensive test reporting and analysis system"""
    
    def __init__(self, db_manager: VIPTestConfigManager):
        self.db_manager = db_manager
        self.logger = self._setup_logging()
        
        # Configure matplotlib and seaborn
        plt.style.use('seaborn-v0_8')
        sns.set_palette("husl")
        
        # Report templates
        self.html_template = self._load_html_template()
        
    def _setup_logging(self) -> logging.Logger:
        """Setup logging for reporting system"""
        logger = logging.getLogger('VIPReporting')
        logger.setLevel(logging.INFO)
        
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            
        return logger
        
    def generate_comprehensive_report(self, config: ReportConfig) -> str:
        """Generate comprehensive test report"""
        
        self.logger.info(f"Generating {config.report_type} report")
        
        # Create output directory
        output_dir = Path(config.output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        
        # Collect data
        report_data = self._collect_report_data(config)
        
        # Generate visualizations
        if config.include_plots:
            plot_paths = self._generate_visualizations(report_data, output_dir, config)
        else:
            plot_paths = {}
            
        # Generate report based on type
        if config.report_type == "summary":
            report_content = self._generate_summary_report(report_data, plot_paths, config)
        elif config.report_type == "detailed":
            report_content = self._generate_detailed_report(report_data, plot_paths, config)
        elif config.report_type == "trend":
            report_content = self._generate_trend_report(report_data, plot_paths, config)
        elif config.report_type == "comparison":
            report_content = self._generate_comparison_report(report_data, plot_paths, config)
        else:
            raise ValueError(f"Unknown report type: {config.report_type}")
            
        # Save report
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        report_filename = f"{config.report_type}_report_{timestamp}.{config.output_format}"
        report_path = output_dir / report_filename
        
        with open(report_path, 'w') as f:
            f.write(report_content)
            
        self.logger.info(f"Report generated: {report_path}")
        return str(report_path)
        
    def _collect_report_data(self, config: ReportConfig) -> Dict[str, Any]:
        """Collect all data needed for report generation"""
        
        end_date = datetime.now()
        start_date = end_date - timedelta(days=config.time_range_days)
        
        data = {
            'config': config,
            'time_range': {
                'start_date': start_date,
                'end_date': end_date,
                'days': config.time_range_days
            }
        }
        
        # Test results summary
        data['test_summary'] = self._get_test_summary_data(start_date, end_date, config)
        
        # Regression results
        data['regression_summary'] = self._get_regression_summary_data(start_date, end_date, config)
        
        # Coverage data
        if config.include_coverage:
            data['coverage_data'] = self._get_coverage_data(start_date, end_date, config)
            
        # Performance data
        if config.include_performance:
            data['performance_data'] = self._get_performance_data(start_date, end_date, config)
            
        # Trend data
        data['trend_data'] = self._get_trend_data(start_date, end_date, config)
        
        # Failure analysis
        data['failure_analysis'] = self._get_failure_analysis_data(start_date, end_date, config)
        
        return data
        
    def _get_test_summary_data(self, start_date: datetime, end_date: datetime, 
                              config: ReportConfig) -> Dict[str, Any]:
        """Get test summary statistics"""
        
        query = """
            SELECT 
                tc.test_name,
                tc.test_type,
                tc.category,
                tc.priority,
                ts.suite_name,
                COUNT(tr.result_id) as total_runs,
                SUM(CASE WHEN tr.status = 'PASS' THEN 1 ELSE 0 END) as passed,
                SUM(CASE WHEN tr.status = 'FAIL' THEN 1 ELSE 0 END) as failed,
                SUM(CASE WHEN tr.status = 'ERROR' THEN 1 ELSE 0 END) as errors,
                SUM(CASE WHEN tr.status = 'TIMEOUT' THEN 1 ELSE 0 END) as timeouts,
                AVG(tr.duration_seconds) as avg_duration,
                AVG(tr.coverage_percentage) as avg_coverage,
                MAX(tr.start_time) as last_run_time
            FROM test_cases tc
            LEFT JOIN test_suites ts ON tc.suite_id = ts.suite_id
            LEFT JOIN test_executions te ON tc.test_id = te.test_id
            LEFT JOIN test_results tr ON te.execution_id = tr.execution_id
            WHERE tr.start_time BETWEEN ? AND ?
        """
        
        params = [start_date, end_date]
        
        # Add filters
        if config.test_suites:
            query += " AND tc.suite_id IN ({})".format(','.join('?' * len(config.test_suites)))
            params.extend(config.test_suites)
            
        if config.test_categories:
            query += " AND tc.category IN ({})".format(','.join('?' * len(config.test_categories)))
            params.extend(config.test_categories)
            
        query += " GROUP BY tc.test_id, tc.test_name, tc.test_type, tc.category, tc.priority, ts.suite_name"
        query += " ORDER BY tc.priority, total_runs DESC"
        
        cursor = self.db_manager.conn.cursor()
        cursor.execute(query, params)
        
        results = [dict(row) for row in cursor.fetchall()]
        
        # Calculate summary statistics
        summary_stats = {
            'total_tests': len(results),
            'total_runs': sum(r['total_runs'] for r in results if r['total_runs']),
            'total_passed': sum(r['passed'] for r in results if r['passed']),
            'total_failed': sum(r['failed'] for r in results if r['failed']),
            'total_errors': sum(r['errors'] for r in results if r['errors']),
            'total_timeouts': sum(r['timeouts'] for r in results if r['timeouts']),
            'avg_duration': np.mean([r['avg_duration'] for r in results if r['avg_duration']]),
            'avg_coverage': np.mean([r['avg_coverage'] for r in results if r['avg_coverage']])
        }
        
        # Calculate pass rate
        total_executions = summary_stats['total_runs']
        if total_executions > 0:
            summary_stats['pass_rate'] = (summary_stats['total_passed'] / total_executions) * 100
        else:
            summary_stats['pass_rate'] = 0
            
        return {
            'summary_stats': summary_stats,
            'test_details': results,
            'by_category': self._group_by_field(results, 'category'),
            'by_type': self._group_by_field(results, 'test_type'),
            'by_priority': self._group_by_field(results, 'priority')
        }
        
    def _get_regression_summary_data(self, start_date: datetime, end_date: datetime,
                                   config: ReportConfig) -> Dict[str, Any]:
        """Get regression summary statistics"""
        
        query = """
            SELECT 
                rr.regression_id,
                rr.regression_name,
                rr.start_time,
                rr.end_time,
                rr.status,
                rr.total_tests,
                rr.passed_tests,
                rr.failed_tests,
                rr.skipped_tests,
                rr.overall_coverage,
                rr.trigger_type,
                ts.suite_name,
                bc.config_name
            FROM regression_runs rr
            LEFT JOIN test_suites ts ON rr.suite_id = ts.suite_id
            LEFT JOIN bus_configs bc ON rr.config_id = bc.config_id
            WHERE rr.start_time BETWEEN ? AND ?
        """
        
        params = [start_date, end_date]
        
        if config.regression_ids:
            query += " AND rr.regression_id IN ({})".format(','.join('?' * len(config.regression_ids)))
            params.extend(config.regression_ids)
            
        query += " ORDER BY rr.start_time DESC"
        
        cursor = self.db_manager.conn.cursor()
        cursor.execute(query, params)
        
        regressions = [dict(row) for row in cursor.fetchall()]
        
        # Calculate regression statistics
        total_regressions = len(regressions)
        completed_regressions = len([r for r in regressions if r['status'] == 'COMPLETED'])
        failed_regressions = len([r for r in regressions if r['status'] == 'FAILED'])
        
        avg_pass_rate = 0
        avg_coverage = 0
        if regressions:
            pass_rates = []
            coverages = []
            for r in regressions:
                if r['total_tests'] and r['total_tests'] > 0:
                    pass_rate = (r['passed_tests'] / r['total_tests']) * 100
                    pass_rates.append(pass_rate)
                if r['overall_coverage']:
                    coverages.append(r['overall_coverage'])
                    
            avg_pass_rate = np.mean(pass_rates) if pass_rates else 0
            avg_coverage = np.mean(coverages) if coverages else 0
            
        return {
            'total_regressions': total_regressions,
            'completed_regressions': completed_regressions,
            'failed_regressions': failed_regressions,
            'success_rate': (completed_regressions / total_regressions * 100) if total_regressions > 0 else 0,
            'avg_pass_rate': avg_pass_rate,
            'avg_coverage': avg_coverage,
            'regression_details': regressions,
            'by_trigger_type': self._group_by_field(regressions, 'trigger_type'),
            'by_status': self._group_by_field(regressions, 'status')
        }
        
    def _get_coverage_data(self, start_date: datetime, end_date: datetime,
                          config: ReportConfig) -> Dict[str, Any]:
        """Get coverage analysis data"""
        
        # Overall coverage trends
        coverage_trend_query = """
            SELECT 
                DATE(tr.start_time) as test_date,
                AVG(tr.coverage_percentage) as avg_coverage,
                MIN(tr.coverage_percentage) as min_coverage,
                MAX(tr.coverage_percentage) as max_coverage,
                COUNT(*) as test_count
            FROM test_results tr
            JOIN test_executions te ON tr.execution_id = te.execution_id
            JOIN test_cases tc ON te.test_id = tc.test_id
            WHERE tr.start_time BETWEEN ? AND ?
              AND tr.coverage_percentage > 0
        """
        
        params = [start_date, end_date]
        
        if config.test_categories:
            coverage_trend_query += " AND tc.category IN ({})".format(','.join('?' * len(config.test_categories)))
            params.extend(config.test_categories)
            
        coverage_trend_query += """
            GROUP BY DATE(tr.start_time)
            ORDER BY test_date
        """
        
        cursor = self.db_manager.conn.cursor()
        cursor.execute(coverage_trend_query, params)
        coverage_trends = [dict(row) for row in cursor.fetchall()]
        
        # Coverage by test category
        coverage_by_category_query = """
            SELECT 
                tc.category,
                AVG(tr.coverage_percentage) as avg_coverage,
                MIN(tr.coverage_percentage) as min_coverage,
                MAX(tr.coverage_percentage) as max_coverage,
                COUNT(*) as test_count
            FROM test_results tr
            JOIN test_executions te ON tr.execution_id = te.execution_id
            JOIN test_cases tc ON te.test_id = tc.test_id
            WHERE tr.start_time BETWEEN ? AND ?
              AND tr.coverage_percentage > 0
            GROUP BY tc.category
            ORDER BY avg_coverage DESC
        """
        
        cursor.execute(coverage_by_category_query, [start_date, end_date])
        coverage_by_category = [dict(row) for row in cursor.fetchall()]
        
        # Detailed coverage metrics
        detailed_coverage_query = """
            SELECT 
                cm.metric_type,
                cm.metric_name,
                AVG(cm.percentage) as avg_percentage,
                MIN(cm.percentage) as min_percentage,
                MAX(cm.percentage) as max_percentage,
                COUNT(*) as sample_count
            FROM coverage_metrics cm
            JOIN test_results tr ON cm.result_id = tr.result_id
            WHERE tr.start_time BETWEEN ? AND ?
            GROUP BY cm.metric_type, cm.metric_name
            ORDER BY cm.metric_type, avg_percentage DESC
        """
        
        cursor.execute(detailed_coverage_query, [start_date, end_date])
        detailed_coverage = [dict(row) for row in cursor.fetchall()]
        
        return {
            'coverage_trends': coverage_trends,
            'coverage_by_category': coverage_by_category,
            'detailed_coverage': detailed_coverage,
            'overall_avg_coverage': np.mean([c['avg_coverage'] for c in coverage_trends]) if coverage_trends else 0
        }
        
    def _get_performance_data(self, start_date: datetime, end_date: datetime,
                            config: ReportConfig) -> Dict[str, Any]:
        """Get performance analysis data"""
        
        # Performance benchmarks
        perf_query = """
            SELECT 
                pb.metric_name,
                pb.unit,
                AVG(pb.value) as avg_value,
                MIN(pb.value) as min_value,
                MAX(pb.value) as max_value,
                STDDEV(pb.value) as std_value,
                COUNT(*) as sample_count,
                AVG(pb.target_value) as target_value
            FROM performance_benchmarks pb
            JOIN test_results tr ON pb.result_id = tr.result_id
            WHERE tr.start_time BETWEEN ? AND ?
            GROUP BY pb.metric_name, pb.unit
            ORDER BY pb.metric_name
        """
        
        cursor = self.db_manager.conn.cursor()
        cursor.execute(perf_query, [start_date, end_date])
        performance_metrics = [dict(row) for row in cursor.fetchall()]
        
        # Performance trends over time
        perf_trend_query = """
            SELECT 
                DATE(tr.start_time) as test_date,
                pb.metric_name,
                AVG(pb.value) as avg_value,
                pb.unit
            FROM performance_benchmarks pb
            JOIN test_results tr ON pb.result_id = tr.result_id
            WHERE tr.start_time BETWEEN ? AND ?
            GROUP BY DATE(tr.start_time), pb.metric_name, pb.unit
            ORDER BY test_date, pb.metric_name
        """
        
        cursor.execute(perf_trend_query, [start_date, end_date])
        performance_trends = [dict(row) for row in cursor.fetchall()]
        
        # Test execution times
        execution_time_query = """
            SELECT 
                tc.category,
                tc.test_type,
                AVG(tr.duration_seconds) as avg_duration,
                MIN(tr.duration_seconds) as min_duration,
                MAX(tr.duration_seconds) as max_duration,
                COUNT(*) as test_count
            FROM test_results tr
            JOIN test_executions te ON tr.execution_id = te.execution_id
            JOIN test_cases tc ON te.test_id = tc.test_id
            WHERE tr.start_time BETWEEN ? AND ?
              AND tr.duration_seconds > 0
            GROUP BY tc.category, tc.test_type
            ORDER BY avg_duration DESC
        """
        
        cursor.execute(execution_time_query, [start_date, end_date])
        execution_times = [dict(row) for row in cursor.fetchall()]
        
        return {
            'performance_metrics': performance_metrics,
            'performance_trends': performance_trends,
            'execution_times': execution_times
        }
        
    def _get_trend_data(self, start_date: datetime, end_date: datetime,
                       config: ReportConfig) -> Dict[str, Any]:
        """Get trend analysis data"""
        
        # Daily test statistics
        daily_stats_query = """
            SELECT 
                DATE(tr.start_time) as test_date,
                COUNT(*) as total_tests,
                SUM(CASE WHEN tr.status = 'PASS' THEN 1 ELSE 0 END) as passed_tests,
                SUM(CASE WHEN tr.status = 'FAIL' THEN 1 ELSE 0 END) as failed_tests,
                SUM(CASE WHEN tr.status = 'ERROR' THEN 1 ELSE 0 END) as error_tests,
                SUM(CASE WHEN tr.status = 'TIMEOUT' THEN 1 ELSE 0 END) as timeout_tests,
                AVG(tr.duration_seconds) as avg_duration,
                AVG(tr.coverage_percentage) as avg_coverage
            FROM test_results tr
            WHERE tr.start_time BETWEEN ? AND ?
            GROUP BY DATE(tr.start_time)
            ORDER BY test_date
        """
        
        cursor = self.db_manager.conn.cursor()
        cursor.execute(daily_stats_query, [start_date, end_date])
        daily_stats = [dict(row) for row in cursor.fetchall()]
        
        # Add pass rate calculation
        for stat in daily_stats:
            if stat['total_tests'] > 0:
                stat['pass_rate'] = (stat['passed_tests'] / stat['total_tests']) * 100
            else:
                stat['pass_rate'] = 0
                
        # Weekly aggregation
        weekly_stats = self._aggregate_to_weekly(daily_stats)
        
        return {
            'daily_stats': daily_stats,
            'weekly_stats': weekly_stats
        }
        
    def _get_failure_analysis_data(self, start_date: datetime, end_date: datetime,
                                 config: ReportConfig) -> Dict[str, Any]:
        """Get failure analysis data"""
        
        # Top failing tests
        failing_tests_query = """
            SELECT 
                tc.test_name,
                tc.category,
                tc.test_type,
                COUNT(*) as total_runs,
                SUM(CASE WHEN tr.status = 'FAIL' THEN 1 ELSE 0 END) as failures,
                SUM(CASE WHEN tr.status = 'ERROR' THEN 1 ELSE 0 END) as errors,
                SUM(CASE WHEN tr.status = 'TIMEOUT' THEN 1 ELSE 0 END) as timeouts
            FROM test_results tr
            JOIN test_executions te ON tr.execution_id = te.execution_id
            JOIN test_cases tc ON te.test_id = tc.test_id
            WHERE tr.start_time BETWEEN ? AND ?
              AND tr.status IN ('FAIL', 'ERROR', 'TIMEOUT')
            GROUP BY tc.test_id, tc.test_name, tc.category, tc.test_type
            ORDER BY (failures + errors + timeouts) DESC
            LIMIT 20
        """
        
        cursor = self.db_manager.conn.cursor()
        cursor.execute(failing_tests_query, [start_date, end_date])
        failing_tests = [dict(row) for row in cursor.fetchall()]
        
        # Calculate failure rates
        for test in failing_tests:
            total_failures = test['failures'] + test['errors'] + test['timeouts']
            test['failure_rate'] = (total_failures / test['total_runs']) * 100
            
        # Failure patterns by category
        failure_by_category_query = """
            SELECT 
                tc.category,
                COUNT(*) as total_runs,
                SUM(CASE WHEN tr.status = 'FAIL' THEN 1 ELSE 0 END) as failures,
                SUM(CASE WHEN tr.status = 'ERROR' THEN 1 ELSE 0 END) as errors,
                SUM(CASE WHEN tr.status = 'TIMEOUT' THEN 1 ELSE 0 END) as timeouts
            FROM test_results tr
            JOIN test_executions te ON tr.execution_id = te.execution_id
            JOIN test_cases tc ON te.test_id = tc.test_id
            WHERE tr.start_time BETWEEN ? AND ?
            GROUP BY tc.category
            ORDER BY tc.category
        """
        
        cursor.execute(failure_by_category_query, [start_date, end_date])
        failure_by_category = [dict(row) for row in cursor.fetchall()]
        
        # Add failure rates
        for category in failure_by_category:
            total_failures = category['failures'] + category['errors'] + category['timeouts']
            if category['total_runs'] > 0:
                category['failure_rate'] = (total_failures / category['total_runs']) * 100
            else:
                category['failure_rate'] = 0
                
        return {
            'failing_tests': failing_tests,
            'failure_by_category': failure_by_category
        }
        
    def _generate_visualizations(self, report_data: Dict[str, Any], 
                               output_dir: Path, config: ReportConfig) -> Dict[str, str]:
        """Generate all visualizations for the report"""
        
        plot_dir = output_dir / "plots"
        plot_dir.mkdir(exist_ok=True)
        
        plot_paths = {}
        
        # Test summary visualizations
        if 'test_summary' in report_data:
            plot_paths.update(self._generate_test_summary_plots(
                report_data['test_summary'], plot_dir))
                
        # Coverage visualizations
        if config.include_coverage and 'coverage_data' in report_data:
            plot_paths.update(self._generate_coverage_plots(
                report_data['coverage_data'], plot_dir))
                
        # Performance visualizations
        if config.include_performance and 'performance_data' in report_data:
            plot_paths.update(self._generate_performance_plots(
                report_data['performance_data'], plot_dir))
                
        # Trend visualizations
        if 'trend_data' in report_data:
            plot_paths.update(self._generate_trend_plots(
                report_data['trend_data'], plot_dir))
                
        # Failure analysis visualizations
        if 'failure_analysis' in report_data:
            plot_paths.update(self._generate_failure_plots(
                report_data['failure_analysis'], plot_dir))
                
        return plot_paths
        
    def _generate_test_summary_plots(self, test_data: Dict[str, Any], 
                                   plot_dir: Path) -> Dict[str, str]:
        """Generate test summary visualizations"""
        
        plots = {}
        
        # Test results pie chart
        if test_data['summary_stats']['total_runs'] > 0:
            fig, ax = plt.subplots(figsize=(10, 8))
            
            labels = ['Passed', 'Failed', 'Errors', 'Timeouts']
            sizes = [
                test_data['summary_stats']['total_passed'],
                test_data['summary_stats']['total_failed'],
                test_data['summary_stats']['total_errors'],
                test_data['summary_stats']['total_timeouts']
            ]
            colors = ['#2ecc71', '#e74c3c', '#f39c12', '#9b59b6']
            
            ax.pie(sizes, labels=labels, colors=colors, autopct='%1.1f%%', startangle=90)
            ax.set_title('Test Results Distribution', fontsize=16, fontweight='bold')
            
            plot_path = plot_dir / "test_results_pie.png"
            plt.savefig(plot_path, dpi=300, bbox_inches='tight')
            plt.close()
            plots['test_results_pie'] = str(plot_path)
            
        # Tests by category bar chart
        if test_data['by_category']:
            categories = list(test_data['by_category'].keys())
            test_counts = [len(test_data['by_category'][cat]) for cat in categories]
            
            fig, ax = plt.subplots(figsize=(12, 6))
            bars = ax.bar(categories, test_counts, color='#3498db')
            ax.set_title('Tests by Category', fontsize=16, fontweight='bold')
            ax.set_xlabel('Category')
            ax.set_ylabel('Number of Tests')
            
            # Add value labels on bars
            for bar in bars:
                height = bar.get_height()
                ax.text(bar.get_x() + bar.get_width()/2., height,
                       f'{int(height)}', ha='center', va='bottom')
                       
            plt.xticks(rotation=45)
            plot_path = plot_dir / "tests_by_category.png"
            plt.savefig(plot_path, dpi=300, bbox_inches='tight')
            plt.close()
            plots['tests_by_category'] = str(plot_path)
            
        return plots
        
    def _generate_coverage_plots(self, coverage_data: Dict[str, Any], 
                               plot_dir: Path) -> Dict[str, str]:
        """Generate coverage visualizations"""
        
        plots = {}
        
        # Coverage trend over time
        if coverage_data['coverage_trends']:
            dates = [item['test_date'] for item in coverage_data['coverage_trends']]
            avg_coverage = [item['avg_coverage'] for item in coverage_data['coverage_trends']]
            
            fig, ax = plt.subplots(figsize=(14, 6))
            ax.plot(dates, avg_coverage, marker='o', linewidth=2, markersize=6)
            ax.set_title('Coverage Trend Over Time', fontsize=16, fontweight='bold')
            ax.set_xlabel('Date')
            ax.set_ylabel('Coverage Percentage')
            ax.grid(True, alpha=0.3)
            
            plt.xticks(rotation=45)
            plot_path = plot_dir / "coverage_trend.png"
            plt.savefig(plot_path, dpi=300, bbox_inches='tight')
            plt.close()
            plots['coverage_trend'] = str(plot_path)
            
        # Coverage by category
        if coverage_data['coverage_by_category']:
            categories = [item['category'] for item in coverage_data['coverage_by_category']]
            avg_coverage = [item['avg_coverage'] for item in coverage_data['coverage_by_category']]
            
            fig, ax = plt.subplots(figsize=(12, 6))
            bars = ax.bar(categories, avg_coverage, color='#27ae60')
            ax.set_title('Average Coverage by Category', fontsize=16, fontweight='bold')
            ax.set_xlabel('Category')
            ax.set_ylabel('Coverage Percentage')
            ax.set_ylim(0, 100)
            
            # Add value labels
            for bar, value in zip(bars, avg_coverage):
                ax.text(bar.get_x() + bar.get_width()/2., bar.get_height() + 1,
                       f'{value:.1f}%', ha='center', va='bottom')
                       
            plt.xticks(rotation=45)
            plot_path = plot_dir / "coverage_by_category.png"
            plt.savefig(plot_path, dpi=300, bbox_inches='tight')
            plt.close()
            plots['coverage_by_category'] = str(plot_path)
            
        return plots
        
    def _generate_performance_plots(self, perf_data: Dict[str, Any], 
                                  plot_dir: Path) -> Dict[str, str]:
        """Generate performance visualizations"""
        
        plots = {}
        
        # Performance metrics comparison
        if perf_data['performance_metrics']:
            metrics = perf_data['performance_metrics']
            
            # Group by metric type
            metric_groups = {}
            for metric in metrics:
                metric_name = metric['metric_name']
                if metric_name not in metric_groups:
                    metric_groups[metric_name] = []
                metric_groups[metric_name].append(metric)
                
            # Create subplot for each metric type
            if metric_groups:
                fig, axes = plt.subplots(len(metric_groups), 1, 
                                       figsize=(12, 4 * len(metric_groups)))
                
                if len(metric_groups) == 1:
                    axes = [axes]
                    
                for i, (metric_name, metric_list) in enumerate(metric_groups.items()):
                    ax = axes[i]
                    
                    values = [m['avg_value'] for m in metric_list]
                    targets = [m['target_value'] for m in metric_list if m['target_value']]
                    labels = [f"{m['metric_name']} ({m['unit']})" for m in metric_list]
                    
                    x_pos = range(len(values))
                    bars = ax.bar(x_pos, values, color='#3498db', alpha=0.7, label='Actual')
                    
                    if targets:
                        ax.bar(x_pos, targets, color='#e74c3c', alpha=0.5, label='Target')
                        
                    ax.set_title(f'Performance Metrics: {metric_name}', fontweight='bold')
                    ax.set_ylabel('Value')
                    ax.set_xticks(x_pos)
                    ax.set_xticklabels(labels, rotation=45)
                    ax.legend()
                    
                plt.tight_layout()
                plot_path = plot_dir / "performance_metrics.png"
                plt.savefig(plot_path, dpi=300, bbox_inches='tight')
                plt.close()
                plots['performance_metrics'] = str(plot_path)
                
        return plots
        
    def _generate_trend_plots(self, trend_data: Dict[str, Any], 
                            plot_dir: Path) -> Dict[str, str]:
        """Generate trend visualizations"""
        
        plots = {}
        
        # Daily pass rate trend
        if trend_data['daily_stats']:
            dates = [item['test_date'] for item in trend_data['daily_stats']]
            pass_rates = [item['pass_rate'] for item in trend_data['daily_stats']]
            
            fig, ax = plt.subplots(figsize=(14, 6))
            ax.plot(dates, pass_rates, marker='o', linewidth=2, markersize=6, color='#2ecc71')
            ax.set_title('Daily Pass Rate Trend', fontsize=16, fontweight='bold')
            ax.set_xlabel('Date')
            ax.set_ylabel('Pass Rate (%)')
            ax.set_ylim(0, 100)
            ax.grid(True, alpha=0.3)
            
            plt.xticks(rotation=45)
            plot_path = plot_dir / "pass_rate_trend.png"
            plt.savefig(plot_path, dpi=300, bbox_inches='tight')
            plt.close()
            plots['pass_rate_trend'] = str(plot_path)
            
        return plots
        
    def _generate_failure_plots(self, failure_data: Dict[str, Any], 
                              plot_dir: Path) -> Dict[str, str]:
        """Generate failure analysis visualizations"""
        
        plots = {}
        
        # Top failing tests
        if failure_data['failing_tests']:
            tests = failure_data['failing_tests'][:10]  # Top 10
            test_names = [t['test_name'][:30] + '...' if len(t['test_name']) > 30 
                         else t['test_name'] for t in tests]
            failure_rates = [t['failure_rate'] for t in tests]
            
            fig, ax = plt.subplots(figsize=(12, 8))
            bars = ax.barh(test_names, failure_rates, color='#e74c3c')
            ax.set_title('Top 10 Failing Tests', fontsize=16, fontweight='bold')
            ax.set_xlabel('Failure Rate (%)')
            ax.set_ylabel('Test Name')
            
            # Add value labels
            for bar, value in zip(bars, failure_rates):
                ax.text(bar.get_width() + 0.5, bar.get_y() + bar.get_height()/2.,
                       f'{value:.1f}%', ha='left', va='center')
                       
            plt.tight_layout()
            plot_path = plot_dir / "top_failing_tests.png"
            plt.savefig(plot_path, dpi=300, bbox_inches='tight')
            plt.close()
            plots['top_failing_tests'] = str(plot_path)
            
        return plots
        
    def _generate_summary_report(self, report_data: Dict[str, Any], 
                               plot_paths: Dict[str, str], config: ReportConfig) -> str:
        """Generate summary report"""
        
        template = """
<!DOCTYPE html>
<html>
<head>
    <title>AXI4 VIP Test Summary Report</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; }
        .header { background-color: #f8f9fa; padding: 20px; border-radius: 5px; }
        .summary-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 20px; margin: 20px 0; }
        .metric-card { background-color: #e8f4f8; padding: 15px; border-radius: 5px; text-align: center; }
        .metric-value { font-size: 2em; font-weight: bold; color: #2c3e50; }
        .metric-label { color: #7f8c8d; margin-top: 5px; }
        .section { margin: 30px 0; }
        .plot { text-align: center; margin: 20px 0; }
        .plot img { max-width: 100%; height: auto; }
        table { border-collapse: collapse; width: 100%; margin: 20px 0; }
        th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
        th { background-color: #f2f2f2; }
        .pass { color: #27ae60; }
        .fail { color: #e74c3c; }
    </style>
</head>
<body>
    <div class="header">
        <h1>AXI4 VIP Test Summary Report</h1>
        <p><strong>Report Period:</strong> {{ report_data.time_range.start_date.strftime('%Y-%m-%d') }} to {{ report_data.time_range.end_date.strftime('%Y-%m-%d') }}</p>
        <p><strong>Generated:</strong> {{ datetime.now().strftime('%Y-%m-%d %H:%M:%S') }}</p>
    </div>
    
    <div class="section">
        <h2>Overall Statistics</h2>
        <div class="summary-grid">
            <div class="metric-card">
                <div class="metric-value">{{ report_data.test_summary.summary_stats.total_tests }}</div>
                <div class="metric-label">Total Tests</div>
            </div>
            <div class="metric-card">
                <div class="metric-value">{{ "%.1f"|format(report_data.test_summary.summary_stats.pass_rate) }}%</div>
                <div class="metric-label">Pass Rate</div>
            </div>
            <div class="metric-card">
                <div class="metric-value">{{ "%.1f"|format(report_data.test_summary.summary_stats.avg_coverage) }}%</div>
                <div class="metric-label">Avg Coverage</div>
            </div>
            <div class="metric-card">
                <div class="metric-value">{{ report_data.regression_summary.total_regressions }}</div>
                <div class="metric-label">Regressions</div>
            </div>
        </div>
    </div>
    
    {% if 'test_results_pie' in plot_paths %}
    <div class="section">
        <h2>Test Results Distribution</h2>
        <div class="plot">
            <img src="{{ plot_paths.test_results_pie }}" alt="Test Results Distribution">
        </div>
    </div>
    {% endif %}
    
    {% if 'tests_by_category' in plot_paths %}
    <div class="section">
        <h2>Tests by Category</h2>
        <div class="plot">
            <img src="{{ plot_paths.tests_by_category }}" alt="Tests by Category">
        </div>
    </div>
    {% endif %}
    
    {% if config.include_coverage and 'coverage_trend' in plot_paths %}
    <div class="section">
        <h2>Coverage Trend</h2>
        <div class="plot">
            <img src="{{ plot_paths.coverage_trend }}" alt="Coverage Trend">
        </div>
    </div>
    {% endif %}
    
</body>
</html>
        """
        
        from jinja2 import Template
        
        jinja_template = Template(template)
        return jinja_template.render(
            report_data=report_data,
            plot_paths=plot_paths,
            config=config,
            datetime=datetime
        )
        
    def _generate_detailed_report(self, report_data: Dict[str, Any], 
                                plot_paths: Dict[str, str], config: ReportConfig) -> str:
        """Generate detailed report with comprehensive analysis"""
        
        # This would be a much more comprehensive template
        # For brevity, returning a basic structure
        summary_content = self._generate_summary_report(report_data, plot_paths, config)
        
        # Add detailed sections
        detailed_sections = """
    <div class="section">
        <h2>Detailed Test Results</h2>
        <table>
            <tr>
                <th>Test Name</th>
                <th>Category</th>
                <th>Runs</th>
                <th>Pass Rate</th>
                <th>Avg Coverage</th>
                <th>Avg Duration</th>
            </tr>
        """
        
        for test in report_data['test_summary']['test_details'][:20]:  # Top 20
            if test['total_runs']:
                pass_rate = (test['passed'] / test['total_runs']) * 100
                detailed_sections += f"""
            <tr>
                <td>{test['test_name']}</td>
                <td>{test['category']}</td>
                <td>{test['total_runs']}</td>
                <td class="{'pass' if pass_rate >= 80 else 'fail'}">{pass_rate:.1f}%</td>
                <td>{test['avg_coverage']:.1f}%</td>
                <td>{test['avg_duration']:.1f}s</td>
            </tr>
                """
                
        detailed_sections += """
        </table>
    </div>
        """
        
        # Insert before closing body tag
        return summary_content.replace('</body>', detailed_sections + '</body>')
        
    def _generate_trend_report(self, report_data: Dict[str, Any], 
                             plot_paths: Dict[str, str], config: ReportConfig) -> str:
        """Generate trend analysis report"""
        
        # Focus on trend visualizations and analysis
        return self._generate_summary_report(report_data, plot_paths, config)
        
    def _generate_comparison_report(self, report_data: Dict[str, Any], 
                                  plot_paths: Dict[str, str], config: ReportConfig) -> str:
        """Generate comparison report between different time periods or configurations"""
        
        # This would compare multiple datasets
        return self._generate_summary_report(report_data, plot_paths, config)
        
    def _group_by_field(self, data: List[Dict], field: str) -> Dict[str, List[Dict]]:
        """Group data by a specific field"""
        grouped = {}
        for item in data:
            key = item.get(field, 'Unknown')
            if key not in grouped:
                grouped[key] = []
            grouped[key].append(item)
        return grouped
        
    def _aggregate_to_weekly(self, daily_stats: List[Dict]) -> List[Dict]:
        """Aggregate daily statistics to weekly"""
        
        if not daily_stats:
            return []
            
        # Convert to pandas for easier aggregation
        df = pd.DataFrame(daily_stats)
        df['test_date'] = pd.to_datetime(df['test_date'])
        df['week'] = df['test_date'].dt.to_period('W')
        
        # Aggregate by week
        weekly = df.groupby('week').agg({
            'total_tests': 'sum',
            'passed_tests': 'sum',
            'failed_tests': 'sum',
            'error_tests': 'sum',
            'timeout_tests': 'sum',
            'avg_duration': 'mean',
            'avg_coverage': 'mean'
        }).reset_index()
        
        # Calculate pass rate
        weekly['pass_rate'] = (weekly['passed_tests'] / weekly['total_tests'] * 100).fillna(0)
        
        # Convert back to dict format
        weekly['week'] = weekly['week'].astype(str)
        return weekly.to_dict('records')
        
    def _load_html_template(self) -> str:
        """Load HTML template for reports"""
        
        # Basic HTML template - in a real implementation, this would be loaded from a file
        return """
<!DOCTYPE html>
<html>
<head>
    <title>{{ title }}</title>
    <style>
        {{ css_styles }}
    </style>
</head>
<body>
    {{ content }}
</body>
</html>
        """

def example_report_generation():
    """Example of generating various reports"""
    
    # Initialize reporting system
    db_manager = VIPTestConfigManager()
    reporter = VIPTestReportingAnalyzer(db_manager)
    
    # Generate summary report
    summary_config = ReportConfig(
        report_type="summary",
        time_range_days=30,
        include_plots=True,
        include_coverage=True,
        include_performance=True,
        output_format="html"
    )
    
    summary_report = reporter.generate_comprehensive_report(summary_config)
    print(f"Summary report generated: {summary_report}")
    
    # Generate detailed report
    detailed_config = ReportConfig(
        report_type="detailed",
        time_range_days=7,
        include_plots=True,
        test_categories=['basic', 'burst', 'exclusive'],
        output_format="html"
    )
    
    detailed_report = reporter.generate_comprehensive_report(detailed_config)
    print(f"Detailed report generated: {detailed_report}")
    
    # Generate trend report
    trend_config = ReportConfig(
        report_type="trend",
        time_range_days=90,
        include_plots=True,
        output_format="html"
    )
    
    trend_report = reporter.generate_comprehensive_report(trend_config)
    print(f"Trend report generated: {trend_report}")

if __name__ == "__main__":
    example_report_generation()