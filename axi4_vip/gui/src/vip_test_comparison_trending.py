#!/usr/bin/env python3

"""
AXI4 VIP Test Result Comparison and Trending System
Advanced comparison and trending analysis for test results with statistical analysis,
benchmark tracking, and predictive capabilities based on tim_axi4_vip architecture.
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
from typing import Dict, List, Any, Optional, Tuple, Union
from pathlib import Path
from dataclasses import dataclass, asdict
import logging
from scipy import stats
from sklearn.linear_model import LinearRegression
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import mean_squared_error, r2_score
import plotly.graph_objects as go
import plotly.express as px
from plotly.subplots import make_subplots
import plotly.offline as pyo
from statsmodels.tsa.seasonal import seasonal_decompose
from statsmodels.tsa.holtwinters import ExponentialSmoothing
import warnings
warnings.filterwarnings('ignore')

from test_config_manager import VIPTestConfigManager

@dataclass
class ComparisonConfig:
    """Configuration for test result comparison"""
    comparison_type: str  # before_after, regression_vs_regression, baseline_vs_current
    baseline_start_date: Optional[datetime] = None
    baseline_end_date: Optional[datetime] = None
    target_start_date: Optional[datetime] = None
    target_end_date: Optional[datetime] = None
    baseline_regression_ids: List[int] = None
    target_regression_ids: List[int] = None
    test_categories: List[str] = None
    metrics_to_compare: List[str] = None
    significance_level: float = 0.05
    
    def __post_init__(self):
        if self.baseline_regression_ids is None:
            self.baseline_regression_ids = []
        if self.target_regression_ids is None:
            self.target_regression_ids = []
        if self.test_categories is None:
            self.test_categories = []
        if self.metrics_to_compare is None:
            self.metrics_to_compare = ['pass_rate', 'coverage', 'duration', 'performance']

@dataclass
class TrendConfig:
    """Configuration for trend analysis"""
    trend_type: str  # linear, polynomial, seasonal, exponential
    lookback_days: int = 90
    forecast_days: int = 30
    metrics: List[str] = None
    confidence_interval: float = 0.95
    detect_anomalies: bool = True
    anomaly_threshold: float = 2.0  # Standard deviations
    
    def __post_init__(self):
        if self.metrics is None:
            self.metrics = ['pass_rate', 'coverage', 'avg_duration']

@dataclass
class StatisticalResult:
    """Statistical analysis result"""
    metric_name: str
    baseline_mean: float
    target_mean: float
    percentage_change: float
    p_value: float
    is_significant: bool
    effect_size: float
    confidence_interval: Tuple[float, float]
    test_type: str
    
class VIPTestComparisonTrending:
    """Advanced test result comparison and trending system"""
    
    def __init__(self, db_manager: VIPTestConfigManager):
        self.db_manager = db_manager
        self.logger = self._setup_logging()
        
        # Configure plotting
        plt.style.use('seaborn-v0_8')
        sns.set_palette("husl")
        
    def _setup_logging(self) -> logging.Logger:
        """Setup logging for comparison system"""
        logger = logging.getLogger('VIPComparison')
        logger.setLevel(logging.INFO)
        
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            
        return logger
        
    def compare_test_results(self, config: ComparisonConfig, 
                           output_dir: str = "/tmp/vip_comparisons") -> Dict[str, Any]:
        """Perform comprehensive test result comparison"""
        
        self.logger.info(f"Performing {config.comparison_type} comparison")
        
        # Create output directory
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Collect baseline and target data
        baseline_data = self._collect_comparison_data(
            config.baseline_start_date, config.baseline_end_date,
            config.baseline_regression_ids, config.test_categories
        )
        
        target_data = self._collect_comparison_data(
            config.target_start_date, config.target_end_date,
            config.target_regression_ids, config.test_categories
        )
        
        # Perform statistical comparisons
        statistical_results = self._perform_statistical_analysis(
            baseline_data, target_data, config
        )
        
        # Generate comparison visualizations
        visualization_paths = self._generate_comparison_visualizations(
            baseline_data, target_data, statistical_results, output_path, config
        )
        
        # Generate comparison report
        report_data = {
            'config': asdict(config),
            'baseline_summary': self._summarize_dataset(baseline_data),
            'target_summary': self._summarize_dataset(target_data),
            'statistical_results': [asdict(result) for result in statistical_results],
            'visualization_paths': visualization_paths,
            'recommendations': self._generate_recommendations(statistical_results)
        }
        
        # Save comparison report
        report_path = output_path / f"comparison_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(report_path, 'w') as f:
            json.dump(report_data, f, indent=2, default=str)
            
        self.logger.info(f"Comparison analysis completed: {report_path}")
        return report_data
        
    def analyze_trends(self, config: TrendConfig, 
                      output_dir: str = "/tmp/vip_trends") -> Dict[str, Any]:
        """Perform comprehensive trend analysis"""
        
        self.logger.info(f"Performing {config.trend_type} trend analysis")
        
        # Create output directory
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Collect historical data
        end_date = datetime.now()
        start_date = end_date - timedelta(days=config.lookback_days)
        
        historical_data = self._collect_trend_data(start_date, end_date, config)
        
        # Perform trend analysis for each metric
        trend_results = {}
        forecasts = {}
        anomalies = {}
        
        for metric in config.metrics:
            if metric in historical_data and len(historical_data[metric]) > 10:
                # Trend analysis
                trend_results[metric] = self._analyze_metric_trend(
                    historical_data[metric], config
                )
                
                # Forecasting
                forecasts[metric] = self._forecast_metric(
                    historical_data[metric], config
                )
                
                # Anomaly detection
                if config.detect_anomalies:
                    anomalies[metric] = self._detect_anomalies(
                        historical_data[metric], config
                    )
                    
        # Generate trend visualizations
        visualization_paths = self._generate_trend_visualizations(
            historical_data, trend_results, forecasts, anomalies, output_path, config
        )
        
        # Compile results
        trend_analysis = {
            'config': asdict(config),
            'historical_data': historical_data,
            'trend_results': trend_results,
            'forecasts': forecasts,
            'anomalies': anomalies,
            'visualization_paths': visualization_paths,
            'insights': self._generate_trend_insights(trend_results, forecasts, anomalies)
        }
        
        # Save trend analysis
        report_path = output_path / f"trend_analysis_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
        with open(report_path, 'w') as f:
            json.dump(trend_analysis, f, indent=2, default=str)
            
        self.logger.info(f"Trend analysis completed: {report_path}")
        return trend_analysis
        
    def _collect_comparison_data(self, start_date: Optional[datetime], 
                               end_date: Optional[datetime],
                               regression_ids: List[int],
                               test_categories: List[str]) -> pd.DataFrame:
        """Collect data for comparison analysis"""
        
        query = """
            SELECT 
                tr.result_id,
                tr.start_time,
                tr.end_time,
                tr.duration_seconds,
                tr.status,
                tr.coverage_percentage,
                tr.assertions_passed,
                tr.assertions_failed,
                tr.warnings_count,
                tr.errors_count,
                tc.test_name,
                tc.test_type,
                tc.category,
                tc.priority,
                ts.suite_name,
                te.seed,
                te.simulator
            FROM test_results tr
            JOIN test_executions te ON tr.execution_id = te.execution_id
            JOIN test_cases tc ON te.test_id = tc.test_id
            LEFT JOIN test_suites ts ON tc.suite_id = ts.suite_id
            WHERE 1=1
        """
        
        params = []
        
        # Add time range filter
        if start_date and end_date:
            query += " AND tr.start_time BETWEEN ? AND ?"
            params.extend([start_date, end_date])
            
        # Add regression filter
        if regression_ids:
            # Find test executions from these regressions
            regression_query = """
                SELECT DISTINCT te.execution_id
                FROM test_executions te
                JOIN test_results tr ON te.execution_id = tr.execution_id
                WHERE tr.result_id IN (
                    SELECT tr2.result_id 
                    FROM test_results tr2
                    WHERE tr2.result_id IN (
                        SELECT result_id FROM test_results 
                        WHERE start_time IN (
                            SELECT start_time FROM regression_runs 
                            WHERE regression_id IN ({})
                        )
                    )
                )
            """.format(','.join('?' * len(regression_ids)))
            
            query += f" AND te.execution_id IN ({regression_query})"
            params.extend(regression_ids)
            
        # Add category filter
        if test_categories:
            query += " AND tc.category IN ({})".format(','.join('?' * len(test_categories)))
            params.extend(test_categories)
            
        query += " ORDER BY tr.start_time"
        
        cursor = self.db_manager.conn.cursor()
        cursor.execute(query, params)
        
        columns = [description[0] for description in cursor.description]
        data = cursor.fetchall()
        
        df = pd.DataFrame(data, columns=columns)
        
        if not df.empty:
            # Convert timestamps
            df['start_time'] = pd.to_datetime(df['start_time'])
            df['end_time'] = pd.to_datetime(df['end_time'])
            
            # Add derived metrics
            df['pass_rate'] = (df['status'] == 'PASS').astype(int)
            df['test_date'] = df['start_time'].dt.date
            
        return df
        
    def _collect_trend_data(self, start_date: datetime, end_date: datetime,
                          config: TrendConfig) -> Dict[str, pd.DataFrame]:
        """Collect data for trend analysis"""
        
        # Daily aggregated metrics
        daily_query = """
            SELECT 
                DATE(tr.start_time) as test_date,
                COUNT(*) as total_tests,
                SUM(CASE WHEN tr.status = 'PASS' THEN 1 ELSE 0 END) as passed_tests,
                AVG(tr.duration_seconds) as avg_duration,
                AVG(tr.coverage_percentage) as avg_coverage,
                SUM(tr.assertions_passed) as total_assertions_passed,
                SUM(tr.assertions_failed) as total_assertions_failed,
                AVG(tr.warnings_count) as avg_warnings,
                AVG(tr.errors_count) as avg_errors
            FROM test_results tr
            WHERE tr.start_time BETWEEN ? AND ?
              AND tr.duration_seconds > 0
            GROUP BY DATE(tr.start_time)
            ORDER BY test_date
        """
        
        cursor = self.db_manager.conn.cursor()
        cursor.execute(daily_query, [start_date, end_date])
        
        daily_data = pd.DataFrame(cursor.fetchall(), 
                                 columns=[desc[0] for desc in cursor.description])
        
        if not daily_data.empty:
            daily_data['test_date'] = pd.to_datetime(daily_data['test_date'])
            daily_data['pass_rate'] = (daily_data['passed_tests'] / daily_data['total_tests'] * 100).fillna(0)
            
        # Performance metrics data
        perf_query = """
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
        
        cursor.execute(perf_query, [start_date, end_date])
        perf_data = pd.DataFrame(cursor.fetchall(),
                               columns=[desc[0] for desc in cursor.description])
        
        if not perf_data.empty:
            perf_data['test_date'] = pd.to_datetime(perf_data['test_date'])
            
        # Organize data by metric
        trend_data = {
            'pass_rate': daily_data[['test_date', 'pass_rate']].set_index('test_date') if not daily_data.empty else pd.DataFrame(),
            'coverage': daily_data[['test_date', 'avg_coverage']].set_index('test_date') if not daily_data.empty else pd.DataFrame(),
            'avg_duration': daily_data[['test_date', 'avg_duration']].set_index('test_date') if not daily_data.empty else pd.DataFrame(),
            'total_tests': daily_data[['test_date', 'total_tests']].set_index('test_date') if not daily_data.empty else pd.DataFrame()
        }
        
        # Add performance metrics
        if not perf_data.empty:
            for metric_name in perf_data['metric_name'].unique():
                metric_df = perf_data[perf_data['metric_name'] == metric_name]
                trend_data[f"perf_{metric_name}"] = metric_df[['test_date', 'avg_value']].set_index('test_date')
                
        return trend_data
        
    def _perform_statistical_analysis(self, baseline_data: pd.DataFrame, 
                                    target_data: pd.DataFrame,
                                    config: ComparisonConfig) -> List[StatisticalResult]:
        """Perform statistical analysis between datasets"""
        
        results = []
        
        for metric in config.metrics_to_compare:
            if metric == 'pass_rate':
                baseline_values = baseline_data['pass_rate'].values
                target_values = target_data['pass_rate'].values
            elif metric == 'coverage':
                baseline_values = baseline_data['coverage_percentage'].dropna().values
                target_values = target_data['coverage_percentage'].dropna().values
            elif metric == 'duration':
                baseline_values = baseline_data['duration_seconds'].dropna().values
                target_values = target_data['duration_seconds'].dropna().values
            else:
                continue
                
            if len(baseline_values) == 0 or len(target_values) == 0:
                continue
                
            # Calculate basic statistics
            baseline_mean = np.mean(baseline_values)
            target_mean = np.mean(target_values)
            percentage_change = ((target_mean - baseline_mean) / baseline_mean * 100) if baseline_mean != 0 else 0
            
            # Perform appropriate statistical test
            if len(baseline_values) > 30 and len(target_values) > 30:
                # Use t-test for large samples
                statistic, p_value = stats.ttest_ind(baseline_values, target_values)
                test_type = "Independent t-test"
            else:
                # Use Mann-Whitney U test for small samples
                statistic, p_value = stats.mannwhitneyu(baseline_values, target_values, alternative='two-sided')
                test_type = "Mann-Whitney U test"
                
            # Calculate effect size (Cohen's d)
            pooled_std = np.sqrt(((len(baseline_values) - 1) * np.var(baseline_values, ddof=1) + 
                                (len(target_values) - 1) * np.var(target_values, ddof=1)) / 
                               (len(baseline_values) + len(target_values) - 2))
            effect_size = (target_mean - baseline_mean) / pooled_std if pooled_std != 0 else 0
            
            # Calculate confidence interval for the difference
            se_diff = pooled_std * np.sqrt(1/len(baseline_values) + 1/len(target_values))
            df = len(baseline_values) + len(target_values) - 2
            t_critical = stats.t.ppf(1 - config.significance_level/2, df)
            margin_error = t_critical * se_diff
            diff = target_mean - baseline_mean
            ci_lower = diff - margin_error
            ci_upper = diff + margin_error
            
            result = StatisticalResult(
                metric_name=metric,
                baseline_mean=baseline_mean,
                target_mean=target_mean,
                percentage_change=percentage_change,
                p_value=p_value,
                is_significant=p_value < config.significance_level,
                effect_size=effect_size,
                confidence_interval=(ci_lower, ci_upper),
                test_type=test_type
            )
            
            results.append(result)
            
        return results
        
    def _analyze_metric_trend(self, data: pd.DataFrame, config: TrendConfig) -> Dict[str, Any]:
        """Analyze trend for a specific metric"""
        
        if data.empty or len(data) < 5:
            return {'error': 'Insufficient data for trend analysis'}
            
        # Prepare data
        data_clean = data.dropna()
        if len(data_clean) < 5:
            return {'error': 'Insufficient valid data points'}
            
        # Convert index to numeric for regression
        x = np.arange(len(data_clean)).reshape(-1, 1)
        y = data_clean.iloc[:, 0].values  # First column contains the metric values
        
        trend_result = {}
        
        # Linear trend analysis
        if config.trend_type in ['linear', 'polynomial']:
            if config.trend_type == 'linear':
                model = LinearRegression()
                model.fit(x, y)
                predictions = model.predict(x)
                
                trend_result['linear'] = {
                    'slope': model.coef_[0],
                    'intercept': model.intercept_,
                    'r_squared': r2_score(y, predictions),
                    'trend_direction': 'increasing' if model.coef_[0] > 0 else 'decreasing',
                    'predictions': predictions.tolist()
                }
                
            elif config.trend_type == 'polynomial':
                # Fit polynomial trend (degree 2)
                poly_features = np.column_stack([x.flatten(), x.flatten()**2])
                model = LinearRegression()
                model.fit(poly_features, y)
                predictions = model.predict(poly_features)
                
                trend_result['polynomial'] = {
                    'coefficients': model.coef_.tolist(),
                    'intercept': model.intercept_,
                    'r_squared': r2_score(y, predictions),
                    'predictions': predictions.tolist()
                }
                
        # Seasonal decomposition (if enough data points)
        if config.trend_type == 'seasonal' and len(data_clean) >= 24:
            try:
                decomposition = seasonal_decompose(data_clean.iloc[:, 0], period=7, extrapolate_trend='freq')
                
                trend_result['seasonal'] = {
                    'trend': decomposition.trend.dropna().tolist(),
                    'seasonal': decomposition.seasonal.dropna().tolist(),
                    'residual': decomposition.resid.dropna().tolist(),
                    'seasonal_strength': np.var(decomposition.seasonal.dropna()) / np.var(y)
                }
            except Exception as e:
                trend_result['seasonal'] = {'error': f'Seasonal decomposition failed: {str(e)}'}
                
        # Exponential smoothing
        if config.trend_type == 'exponential' and len(data_clean) >= 10:
            try:
                model = ExponentialSmoothing(data_clean.iloc[:, 0], trend='add')
                fitted_model = model.fit()
                
                trend_result['exponential'] = {
                    'smoothing_level': fitted_model.params['smoothing_level'],
                    'smoothing_trend': fitted_model.params.get('smoothing_trend', None),
                    'fitted_values': fitted_model.fittedvalues.tolist(),
                    'aic': fitted_model.aic
                }
            except Exception as e:
                trend_result['exponential'] = {'error': f'Exponential smoothing failed: {str(e)}'}
                
        # Basic statistics
        trend_result['statistics'] = {
            'mean': np.mean(y),
            'std': np.std(y),
            'min': np.min(y),
            'max': np.max(y),
            'trend_strength': np.corrcoef(x.flatten(), y)[0, 1] if len(y) > 1 else 0,
            'data_points': len(y)
        }
        
        return trend_result
        
    def _forecast_metric(self, data: pd.DataFrame, config: TrendConfig) -> Dict[str, Any]:
        """Generate forecasts for a metric"""
        
        if data.empty or len(data) < 10:
            return {'error': 'Insufficient data for forecasting'}
            
        data_clean = data.dropna()
        if len(data_clean) < 10:
            return {'error': 'Insufficient valid data points'}
            
        forecast_result = {}
        
        try:
            # Simple linear extrapolation
            x = np.arange(len(data_clean))
            y = data_clean.iloc[:, 0].values
            
            model = LinearRegression()
            model.fit(x.reshape(-1, 1), y)
            
            # Generate future points
            future_x = np.arange(len(data_clean), len(data_clean) + config.forecast_days)
            future_predictions = model.predict(future_x.reshape(-1, 1))
            
            # Calculate prediction intervals
            mse = mean_squared_error(y, model.predict(x.reshape(-1, 1)))
            std_error = np.sqrt(mse)
            z_score = stats.norm.ppf(1 - (1 - config.confidence_interval) / 2)
            
            forecast_result['linear'] = {
                'predictions': future_predictions.tolist(),
                'lower_bound': (future_predictions - z_score * std_error).tolist(),
                'upper_bound': (future_predictions + z_score * std_error).tolist(),
                'forecast_dates': [(data_clean.index[-1] + timedelta(days=i+1)).strftime('%Y-%m-%d') 
                                 for i in range(config.forecast_days)]
            }
            
            # Exponential smoothing forecast
            if len(data_clean) >= 20:
                model_exp = ExponentialSmoothing(y, trend='add')
                fitted_model = model_exp.fit()
                forecast_exp = fitted_model.forecast(config.forecast_days)
                
                forecast_result['exponential'] = {
                    'predictions': forecast_exp.tolist(),
                    'model_params': dict(fitted_model.params)
                }
                
        except Exception as e:
            forecast_result['error'] = f'Forecasting failed: {str(e)}'
            
        return forecast_result
        
    def _detect_anomalies(self, data: pd.DataFrame, config: TrendConfig) -> Dict[str, Any]:
        """Detect anomalies in the data"""
        
        if data.empty or len(data) < 10:
            return {'error': 'Insufficient data for anomaly detection'}
            
        data_clean = data.dropna()
        values = data_clean.iloc[:, 0].values
        
        # Z-score based anomaly detection
        z_scores = np.abs(stats.zscore(values))
        anomaly_indices = np.where(z_scores > config.anomaly_threshold)[0]
        
        # IQR based anomaly detection
        q1 = np.percentile(values, 25)
        q3 = np.percentile(values, 75)
        iqr = q3 - q1
        lower_bound = q1 - 1.5 * iqr
        upper_bound = q3 + 1.5 * iqr
        
        iqr_anomaly_indices = np.where((values < lower_bound) | (values > upper_bound))[0]
        
        anomalies = {
            'z_score_anomalies': {
                'indices': anomaly_indices.tolist(),
                'values': values[anomaly_indices].tolist(),
                'dates': [data_clean.index[i].strftime('%Y-%m-%d') for i in anomaly_indices],
                'z_scores': z_scores[anomaly_indices].tolist()
            },
            'iqr_anomalies': {
                'indices': iqr_anomaly_indices.tolist(),
                'values': values[iqr_anomaly_indices].tolist(),
                'dates': [data_clean.index[i].strftime('%Y-%m-%d') for i in iqr_anomaly_indices],
                'bounds': {'lower': lower_bound, 'upper': upper_bound}
            },
            'statistics': {
                'total_points': len(values),
                'z_score_anomalies': len(anomaly_indices),
                'iqr_anomalies': len(iqr_anomaly_indices),
                'anomaly_rate': len(set(anomaly_indices) | set(iqr_anomaly_indices)) / len(values) * 100
            }
        }
        
        return anomalies
        
    def _generate_comparison_visualizations(self, baseline_data: pd.DataFrame,
                                          target_data: pd.DataFrame,
                                          statistical_results: List[StatisticalResult],
                                          output_dir: Path,
                                          config: ComparisonConfig) -> Dict[str, str]:
        """Generate comparison visualizations"""
        
        plot_paths = {}
        
        # Comparison summary plot
        if statistical_results:
            fig, axes = plt.subplots(2, 2, figsize=(15, 12))
            fig.suptitle(f'{config.comparison_type.replace("_", " ").title()} Comparison', fontsize=16)
            
            metrics = [r.metric_name for r in statistical_results]
            baseline_means = [r.baseline_mean for r in statistical_results]
            target_means = [r.target_mean for r in statistical_results]
            percentage_changes = [r.percentage_change for r in statistical_results]
            
            # Metric comparison
            x_pos = np.arange(len(metrics))
            width = 0.35
            
            axes[0, 0].bar(x_pos - width/2, baseline_means, width, label='Baseline', alpha=0.7)
            axes[0, 0].bar(x_pos + width/2, target_means, width, label='Target', alpha=0.7)
            axes[0, 0].set_xlabel('Metrics')
            axes[0, 0].set_ylabel('Values')
            axes[0, 0].set_title('Metric Comparison')
            axes[0, 0].set_xticks(x_pos)
            axes[0, 0].set_xticklabels(metrics, rotation=45)
            axes[0, 0].legend()
            
            # Percentage change
            colors = ['green' if x > 0 else 'red' for x in percentage_changes]
            axes[0, 1].bar(metrics, percentage_changes, color=colors, alpha=0.7)
            axes[0, 1].set_xlabel('Metrics')
            axes[0, 1].set_ylabel('Percentage Change (%)')
            axes[0, 1].set_title('Percentage Change')
            axes[0, 1].axhline(y=0, color='black', linestyle='-', alpha=0.3)
            plt.setp(axes[0, 1].xaxis.get_majorticklabels(), rotation=45)
            
            # Statistical significance
            p_values = [r.p_value for r in statistical_results]
            significance = ['Significant' if r.is_significant else 'Not Significant' 
                          for r in statistical_results]
            
            axes[1, 0].bar(metrics, p_values, alpha=0.7)
            axes[1, 0].axhline(y=config.significance_level, color='red', linestyle='--', 
                             label=f'α = {config.significance_level}')
            axes[1, 0].set_xlabel('Metrics')
            axes[1, 0].set_ylabel('p-value')
            axes[1, 0].set_title('Statistical Significance')
            axes[1, 0].legend()
            plt.setp(axes[1, 0].xaxis.get_majorticklabels(), rotation=45)
            
            # Effect sizes
            effect_sizes = [r.effect_size for r in statistical_results]
            axes[1, 1].bar(metrics, effect_sizes, alpha=0.7)
            axes[1, 1].set_xlabel('Metrics')
            axes[1, 1].set_ylabel("Cohen's d")
            axes[1, 1].set_title('Effect Size')
            axes[1, 1].axhline(y=0.2, color='yellow', linestyle='--', alpha=0.5, label='Small')
            axes[1, 1].axhline(y=0.5, color='orange', linestyle='--', alpha=0.5, label='Medium')
            axes[1, 1].axhline(y=0.8, color='red', linestyle='--', alpha=0.5, label='Large')
            axes[1, 1].legend()
            plt.setp(axes[1, 1].xaxis.get_majorticklabels(), rotation=45)
            
            plt.tight_layout()
            plot_path = output_dir / "comparison_summary.png"
            plt.savefig(plot_path, dpi=300, bbox_inches='tight')
            plt.close()
            plot_paths['comparison_summary'] = str(plot_path)
            
        return plot_paths
        
    def _generate_trend_visualizations(self, historical_data: Dict[str, pd.DataFrame],
                                     trend_results: Dict[str, Any],
                                     forecasts: Dict[str, Any],
                                     anomalies: Dict[str, Any],
                                     output_dir: Path,
                                     config: TrendConfig) -> Dict[str, str]:
        """Generate trend visualizations"""
        
        plot_paths = {}
        
        for metric, data in historical_data.items():
            if data.empty or metric not in trend_results:
                continue
                
            fig, axes = plt.subplots(2, 2, figsize=(16, 12))
            fig.suptitle(f'Trend Analysis: {metric.replace("_", " ").title()}', fontsize=16)
            
            # Original data with trend
            axes[0, 0].plot(data.index, data.iloc[:, 0], 'o-', alpha=0.7, label='Actual')
            
            if 'linear' in trend_results[metric]:
                trend_data = trend_results[metric]['linear']
                axes[0, 0].plot(data.index, trend_data['predictions'], '--', 
                              label=f"Linear Trend (R² = {trend_data['r_squared']:.3f})")
                              
            axes[0, 0].set_title('Historical Data with Trend')
            axes[0, 0].set_ylabel('Value')
            axes[0, 0].legend()
            axes[0, 0].grid(True, alpha=0.3)
            
            # Forecast
            if metric in forecasts and 'linear' in forecasts[metric]:
                forecast_data = forecasts[metric]['linear']
                
                # Plot historical data
                axes[0, 1].plot(data.index, data.iloc[:, 0], 'o-', alpha=0.7, label='Historical')
                
                # Plot forecast
                last_date = data.index[-1]
                forecast_dates = pd.date_range(start=last_date + pd.Timedelta(days=1), 
                                             periods=len(forecast_data['predictions']))
                
                axes[0, 1].plot(forecast_dates, forecast_data['predictions'], 'r--', 
                              label='Forecast')
                axes[0, 1].fill_between(forecast_dates, 
                                      forecast_data['lower_bound'],
                                      forecast_data['upper_bound'], 
                                      alpha=0.2, color='red', 
                                      label=f'{config.confidence_interval*100:.0f}% CI')
                                      
                axes[0, 1].set_title(f'Forecast ({config.forecast_days} days)')
                axes[0, 1].set_ylabel('Value')
                axes[0, 1].legend()
                axes[0, 1].grid(True, alpha=0.3)
                
            # Anomalies
            if metric in anomalies:
                anomaly_data = anomalies[metric]
                
                axes[1, 0].plot(data.index, data.iloc[:, 0], 'b-', alpha=0.7, label='Normal')
                
                # Mark Z-score anomalies
                if anomaly_data['z_score_anomalies']['indices']:
                    anomaly_indices = anomaly_data['z_score_anomalies']['indices']
                    axes[1, 0].scatter([data.index[i] for i in anomaly_indices],
                                     [data.iloc[i, 0] for i in anomaly_indices],
                                     color='red', s=50, label='Z-score Anomalies')
                                     
                # Mark IQR anomalies  
                if anomaly_data['iqr_anomalies']['indices']:
                    iqr_indices = anomaly_data['iqr_anomalies']['indices']
                    axes[1, 0].scatter([data.index[i] for i in iqr_indices],
                                     [data.iloc[i, 0] for i in iqr_indices],
                                     color='orange', s=30, marker='^', label='IQR Anomalies')
                                     
                axes[1, 0].set_title('Anomaly Detection')
                axes[1, 0].set_ylabel('Value')
                axes[1, 0].legend()
                axes[1, 0].grid(True, alpha=0.3)
                
            # Statistics summary
            if 'statistics' in trend_results[metric]:
                stats_data = trend_results[metric]['statistics']
                
                stats_text = f"""
Statistics Summary:
Mean: {stats_data['mean']:.2f}
Std Dev: {stats_data['std']:.2f}
Min: {stats_data['min']:.2f}
Max: {stats_data['max']:.2f}
Trend Strength: {stats_data['trend_strength']:.3f}
Data Points: {stats_data['data_points']}
                """
                
                axes[1, 1].text(0.1, 0.5, stats_text, transform=axes[1, 1].transAxes,
                               fontsize=12, verticalalignment='center',
                               bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.8))
                axes[1, 1].set_title('Statistics Summary')
                axes[1, 1].axis('off')
                
            plt.tight_layout()
            plot_path = output_dir / f"trend_{metric}.png"
            plt.savefig(plot_path, dpi=300, bbox_inches='tight')
            plt.close()
            plot_paths[f'trend_{metric}'] = str(plot_path)
            
        return plot_paths
        
    def _summarize_dataset(self, data: pd.DataFrame) -> Dict[str, Any]:
        """Generate summary statistics for a dataset"""
        
        if data.empty:
            return {'error': 'No data available'}
            
        summary = {
            'total_records': len(data),
            'date_range': {
                'start': data['start_time'].min().strftime('%Y-%m-%d') if 'start_time' in data.columns else None,
                'end': data['start_time'].max().strftime('%Y-%m-%d') if 'start_time' in data.columns else None
            },
            'pass_rate': data['pass_rate'].mean() * 100 if 'pass_rate' in data.columns else None,
            'avg_coverage': data['coverage_percentage'].mean() if 'coverage_percentage' in data.columns else None,
            'avg_duration': data['duration_seconds'].mean() if 'duration_seconds' in data.columns else None,
            'categories': data['category'].value_counts().to_dict() if 'category' in data.columns else {},
            'test_types': data['test_type'].value_counts().to_dict() if 'test_type' in data.columns else {}
        }
        
        return summary
        
    def _generate_recommendations(self, statistical_results: List[StatisticalResult]) -> List[str]:
        """Generate recommendations based on statistical analysis"""
        
        recommendations = []
        
        for result in statistical_results:
            if result.is_significant:
                if result.percentage_change > 5:
                    recommendations.append(
                        f"{result.metric_name}: Significant improvement of {result.percentage_change:.1f}% detected. "
                        f"Consider investigating what changes led to this improvement."
                    )
                elif result.percentage_change < -5:
                    recommendations.append(
                        f"{result.metric_name}: Significant degradation of {abs(result.percentage_change):.1f}% detected. "
                        f"Immediate investigation recommended."
                    )
                    
            # Effect size recommendations
            if abs(result.effect_size) > 0.8:
                recommendations.append(
                    f"{result.metric_name}: Large effect size ({result.effect_size:.2f}) indicates "
                    f"substantial practical difference between datasets."
                )
                
        if not recommendations:
            recommendations.append("No significant changes detected in the analyzed metrics.")
            
        return recommendations
        
    def _generate_trend_insights(self, trend_results: Dict[str, Any],
                               forecasts: Dict[str, Any],
                               anomalies: Dict[str, Any]) -> List[str]:
        """Generate insights from trend analysis"""
        
        insights = []
        
        for metric, results in trend_results.items():
            if 'statistics' in results:
                stats = results['statistics']
                
                # Trend direction insight
                if 'linear' in results:
                    linear = results['linear']
                    if linear['trend_direction'] == 'increasing':
                        insights.append(f"{metric}: Shows positive upward trend (slope: {linear['slope']:.4f})")
                    else:
                        insights.append(f"{metric}: Shows downward trend (slope: {linear['slope']:.4f})")
                        
                # Variability insight
                cv = stats['std'] / stats['mean'] if stats['mean'] != 0 else 0
                if cv > 0.2:
                    insights.append(f"{metric}: High variability detected (CV: {cv:.2f})")
                elif cv < 0.05:
                    insights.append(f"{metric}: Very stable metric (CV: {cv:.2f})")
                    
            # Anomaly insights
            if metric in anomalies and 'statistics' in anomalies[metric]:
                anomaly_stats = anomalies[metric]['statistics']
                if anomaly_stats['anomaly_rate'] > 10:
                    insights.append(f"{metric}: High anomaly rate ({anomaly_stats['anomaly_rate']:.1f}%) "
                                  f"suggests unstable performance")
                                  
        return insights

def example_comparison_trending():
    """Example of using comparison and trending analysis"""
    
    # Initialize system
    db_manager = VIPTestConfigManager()
    analyzer = VIPTestComparisonTrending(db_manager)
    
    # Comparison example
    comparison_config = ComparisonConfig(
        comparison_type="before_after",
        baseline_start_date=datetime.now() - timedelta(days=60),
        baseline_end_date=datetime.now() - timedelta(days=30),
        target_start_date=datetime.now() - timedelta(days=30),
        target_end_date=datetime.now(),
        test_categories=['basic', 'burst', 'exclusive'],
        metrics_to_compare=['pass_rate', 'coverage', 'duration']
    )
    
    comparison_results = analyzer.compare_test_results(comparison_config)
    print(f"Comparison analysis completed")
    
    # Trend analysis example
    trend_config = TrendConfig(
        trend_type="linear",
        lookback_days=90,
        forecast_days=14,
        metrics=['pass_rate', 'coverage', 'avg_duration'],
        detect_anomalies=True
    )
    
    trend_results = analyzer.analyze_trends(trend_config)
    print(f"Trend analysis completed")

if __name__ == "__main__":
    example_comparison_trending()