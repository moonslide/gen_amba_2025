#!/usr/bin/env python3

"""
AXI4 VIP CI/CD Integration Hooks
Comprehensive CI/CD integration system with support for multiple platforms,
automated test triggering, and result reporting based on tim_axi4_vip architecture.
"""

import os
import sys
import json
import yaml
import subprocess
import requests
import time
import threading
from datetime import datetime, timedelta
from typing import Dict, List, Any, Optional, Tuple, Union, Callable
from pathlib import Path
from dataclasses import dataclass, asdict
from enum import Enum
import logging
import hashlib
import base64
from urllib.parse import urljoin
import tempfile
import shutil
from abc import ABC, abstractmethod

from test_config_manager import VIPTestConfigManager
from vip_test_execution_framework import VIPTestExecutionFramework, TestExecution, TestStatus
from vip_regression_manager import VIPRegressionManager, RegressionConfig, RegressionType

class CIPlatform(Enum):
    """Supported CI/CD platforms"""
    JENKINS = "jenkins"
    GITHUB_ACTIONS = "github_actions"
    GITLAB_CI = "gitlab_ci"
    AZURE_DEVOPS = "azure_devops"
    CIRCLECI = "circleci"
    BAMBOO = "bamboo"
    TEAMCITY = "teamcity"

class TriggerEvent(Enum):
    """CI/CD trigger events"""
    COMMIT = "commit"
    PULL_REQUEST = "pull_request"
    MERGE_REQUEST = "merge_request"
    RELEASE = "release"
    SCHEDULED = "scheduled"
    MANUAL = "manual"

class TestResult(Enum):
    """Test result status for CI/CD reporting"""
    SUCCESS = "success"
    FAILURE = "failure"
    ERROR = "error"
    PENDING = "pending"
    CANCELLED = "cancelled"

@dataclass
class CIConfig:
    """CI/CD platform configuration"""
    platform: CIPlatform
    server_url: str
    auth_token: str
    project_id: str
    webhook_secret: Optional[str] = None
    timeout_minutes: int = 120
    retry_attempts: int = 3
    notification_channels: List[str] = None
    
    def __post_init__(self):
        if self.notification_channels is None:
            self.notification_channels = []

@dataclass
class TriggerConfig:
    """Test trigger configuration"""
    trigger_events: List[TriggerEvent]
    test_suite_mapping: Dict[str, int]  # event -> suite_id
    regression_type_mapping: Dict[str, RegressionType]  # event -> regression type
    branch_filters: List[str] = None
    path_filters: List[str] = None
    skip_ci_patterns: List[str] = None
    
    def __post_init__(self):
        if self.branch_filters is None:
            self.branch_filters = ["main", "master", "develop"]
        if self.path_filters is None:
            self.path_filters = []
        if self.skip_ci_patterns is None:
            self.skip_ci_patterns = ["[skip ci]", "[ci skip]", "[skip tests]"]

@dataclass
class CIEvent:
    """CI/CD event data"""
    event_type: TriggerEvent
    repository: str
    branch: str
    commit_hash: str
    commit_message: str
    author: str
    timestamp: datetime
    pull_request_id: Optional[str] = None
    changed_files: List[str] = None
    
    def __post_init__(self):
        if self.changed_files is None:
            self.changed_files = []

class CIPlatformAdapter(ABC):
    """Abstract base class for CI platform adapters"""
    
    @abstractmethod
    def authenticate(self, config: CIConfig) -> bool:
        """Authenticate with the CI platform"""
        pass
        
    @abstractmethod
    def register_webhook(self, config: CIConfig, webhook_url: str) -> bool:
        """Register webhook for receiving events"""
        pass
        
    @abstractmethod
    def update_status(self, config: CIConfig, commit_hash: str, 
                     status: TestResult, description: str, 
                     target_url: Optional[str] = None) -> bool:
        """Update commit status"""
        pass
        
    @abstractmethod
    def post_comment(self, config: CIConfig, pull_request_id: str, 
                    comment: str) -> bool:
        """Post comment on pull request"""
        pass
        
    @abstractmethod
    def create_deployment_status(self, config: CIConfig, deployment_id: str,
                               status: TestResult, description: str) -> bool:
        """Create deployment status"""
        pass

class GitHubAdapter(CIPlatformAdapter):
    """GitHub Actions adapter"""
    
    def __init__(self):
        self.api_base = "https://api.github.com"
        
    def authenticate(self, config: CIConfig) -> bool:
        """Authenticate with GitHub API"""
        try:
            headers = {
                "Authorization": f"token {config.auth_token}",
                "Accept": "application/vnd.github.v3+json"
            }
            
            response = requests.get(f"{self.api_base}/user", headers=headers)
            return response.status_code == 200
        except Exception:
            return False
            
    def register_webhook(self, config: CIConfig, webhook_url: str) -> bool:
        """Register webhook with GitHub repository"""
        try:
            headers = {
                "Authorization": f"token {config.auth_token}",
                "Accept": "application/vnd.github.v3+json"
            }
            
            webhook_data = {
                "config": {
                    "url": webhook_url,
                    "content_type": "json",
                    "secret": config.webhook_secret
                },
                "events": ["push", "pull_request", "release"],
                "active": True
            }
            
            url = f"{self.api_base}/repos/{config.project_id}/hooks"
            response = requests.post(url, headers=headers, json=webhook_data)
            return response.status_code == 201
        except Exception:
            return False
            
    def update_status(self, config: CIConfig, commit_hash: str, 
                     status: TestResult, description: str,
                     target_url: Optional[str] = None) -> bool:
        """Update commit status on GitHub"""
        try:
            headers = {
                "Authorization": f"token {config.auth_token}",
                "Accept": "application/vnd.github.v3+json"
            }
            
            status_data = {
                "state": self._map_status(status),
                "description": description,
                "context": "vip-tests"
            }
            
            if target_url:
                status_data["target_url"] = target_url
                
            url = f"{self.api_base}/repos/{config.project_id}/statuses/{commit_hash}"
            response = requests.post(url, headers=headers, json=status_data)
            return response.status_code == 201
        except Exception:
            return False
            
    def post_comment(self, config: CIConfig, pull_request_id: str, 
                    comment: str) -> bool:
        """Post comment on GitHub pull request"""
        try:
            headers = {
                "Authorization": f"token {config.auth_token}",
                "Accept": "application/vnd.github.v3+json"
            }
            
            comment_data = {"body": comment}
            url = f"{self.api_base}/repos/{config.project_id}/issues/{pull_request_id}/comments"
            response = requests.post(url, headers=headers, json=comment_data)
            return response.status_code == 201
        except Exception:
            return False
            
    def create_deployment_status(self, config: CIConfig, deployment_id: str,
                               status: TestResult, description: str) -> bool:
        """Create deployment status on GitHub"""
        try:
            headers = {
                "Authorization": f"token {config.auth_token}",
                "Accept": "application/vnd.github.v3+json"
            }
            
            status_data = {
                "state": self._map_status(status),
                "description": description
            }
            
            url = f"{self.api_base}/repos/{config.project_id}/deployments/{deployment_id}/statuses"
            response = requests.post(url, headers=headers, json=status_data)
            return response.status_code == 201
        except Exception:
            return False
            
    def _map_status(self, status: TestResult) -> str:
        """Map internal status to GitHub status"""
        mapping = {
            TestResult.SUCCESS: "success",
            TestResult.FAILURE: "failure",
            TestResult.ERROR: "error",
            TestResult.PENDING: "pending"
        }
        return mapping.get(status, "error")

class GitLabAdapter(CIPlatformAdapter):
    """GitLab CI adapter"""
    
    def __init__(self):
        self.api_base = None  # Set based on config
        
    def authenticate(self, config: CIConfig) -> bool:
        """Authenticate with GitLab API"""
        try:
            self.api_base = f"{config.server_url}/api/v4"
            headers = {"Private-Token": config.auth_token}
            
            response = requests.get(f"{self.api_base}/user", headers=headers)
            return response.status_code == 200
        except Exception:
            return False
            
    def register_webhook(self, config: CIConfig, webhook_url: str) -> bool:
        """Register webhook with GitLab project"""
        try:
            headers = {"Private-Token": config.auth_token}
            
            webhook_data = {
                "url": webhook_url,
                "push_events": True,
                "merge_requests_events": True,
                "tag_push_events": True,
                "token": config.webhook_secret
            }
            
            url = f"{self.api_base}/projects/{config.project_id}/hooks"
            response = requests.post(url, headers=headers, json=webhook_data)
            return response.status_code == 201
        except Exception:
            return False
            
    def update_status(self, config: CIConfig, commit_hash: str, 
                     status: TestResult, description: str,
                     target_url: Optional[str] = None) -> bool:
        """Update commit status on GitLab"""
        try:
            headers = {"Private-Token": config.auth_token}
            
            status_data = {
                "state": self._map_status(status),
                "description": description,
                "name": "vip-tests"
            }
            
            if target_url:
                status_data["target_url"] = target_url
                
            url = f"{self.api_base}/projects/{config.project_id}/statuses/{commit_hash}"
            response = requests.post(url, headers=headers, json=status_data)
            return response.status_code == 201
        except Exception:
            return False
            
    def post_comment(self, config: CIConfig, pull_request_id: str, 
                    comment: str) -> bool:
        """Post comment on GitLab merge request"""
        try:
            headers = {"Private-Token": config.auth_token}
            
            comment_data = {"body": comment}
            url = f"{self.api_base}/projects/{config.project_id}/merge_requests/{pull_request_id}/notes"
            response = requests.post(url, headers=headers, json=comment_data)
            return response.status_code == 201
        except Exception:
            return False
            
    def create_deployment_status(self, config: CIConfig, deployment_id: str,
                               status: TestResult, description: str) -> bool:
        """Create deployment status on GitLab"""
        # GitLab deployment status implementation
        return True
        
    def _map_status(self, status: TestResult) -> str:
        """Map internal status to GitLab status"""
        mapping = {
            TestResult.SUCCESS: "success",
            TestResult.FAILURE: "failed",
            TestResult.ERROR: "failed",
            TestResult.PENDING: "running"
        }
        return mapping.get(status, "failed")

class JenkinsAdapter(CIPlatformAdapter):
    """Jenkins adapter"""
    
    def authenticate(self, config: CIConfig) -> bool:
        """Authenticate with Jenkins"""
        try:
            auth = (config.auth_token.split(':')[0], config.auth_token.split(':')[1])
            response = requests.get(f"{config.server_url}/api/json", auth=auth)
            return response.status_code == 200
        except Exception:
            return False
            
    def register_webhook(self, config: CIConfig, webhook_url: str) -> bool:
        """Register webhook with Jenkins"""
        # Jenkins webhook registration would be job-specific
        return True
        
    def update_status(self, config: CIConfig, commit_hash: str, 
                     status: TestResult, description: str,
                     target_url: Optional[str] = None) -> bool:
        """Update build status in Jenkins"""
        # Jenkins status update implementation
        return True
        
    def post_comment(self, config: CIConfig, pull_request_id: str, 
                    comment: str) -> bool:
        """Post comment via Jenkins"""
        # Jenkins comment posting implementation
        return True
        
    def create_deployment_status(self, config: CIConfig, deployment_id: str,
                               status: TestResult, description: str) -> bool:
        """Create deployment status in Jenkins"""
        return True

class VIPCICDIntegration:
    """Main CI/CD integration system"""
    
    def __init__(self, db_manager: VIPTestConfigManager,
                 execution_framework: VIPTestExecutionFramework,
                 regression_manager: VIPRegressionManager):
        self.db_manager = db_manager
        self.execution_framework = execution_framework
        self.regression_manager = regression_manager
        
        # Setup logging
        self.logger = self._setup_logging()
        
        # Platform adapters
        self.adapters = {
            CIPlatform.GITHUB_ACTIONS: GitHubAdapter(),
            CIPlatform.GITLAB_CI: GitLabAdapter(),
            CIPlatform.JENKINS: JenkinsAdapter()
        }
        
        # Active configurations
        self.ci_configs: Dict[str, CIConfig] = {}
        self.trigger_configs: Dict[str, TriggerConfig] = {}
        
        # Event processing
        self.event_queue = []
        self.processing_thread = None
        self.shutdown_event = threading.Event()
        
        # Result callbacks
        self.result_callbacks: List[Callable] = []
        
    def _setup_logging(self) -> logging.Logger:
        """Setup logging for CI/CD integration"""
        logger = logging.getLogger('VIPCIIntegration')
        logger.setLevel(logging.INFO)
        
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            
        return logger
        
    def register_ci_platform(self, name: str, ci_config: CIConfig, 
                           trigger_config: TriggerConfig) -> bool:
        """Register a CI/CD platform configuration"""
        
        try:
            # Authenticate with platform
            adapter = self.adapters.get(ci_config.platform)
            if not adapter:
                self.logger.error(f"Unsupported CI platform: {ci_config.platform}")
                return False
                
            if not adapter.authenticate(ci_config):
                self.logger.error(f"Authentication failed for {ci_config.platform}")
                return False
                
            # Store configurations
            self.ci_configs[name] = ci_config
            self.trigger_configs[name] = trigger_config
            
            self.logger.info(f"Registered CI platform: {name}")
            return True
            
        except Exception as e:
            self.logger.error(f"Failed to register CI platform {name}: {e}")
            return False
            
    def setup_webhooks(self, webhook_base_url: str) -> Dict[str, bool]:
        """Setup webhooks for all registered platforms"""
        
        results = {}
        
        for name, ci_config in self.ci_configs.items():
            try:
                webhook_url = f"{webhook_base_url}/webhook/{name}"
                adapter = self.adapters[ci_config.platform]
                
                success = adapter.register_webhook(ci_config, webhook_url)
                results[name] = success
                
                if success:
                    self.logger.info(f"Webhook registered for {name}: {webhook_url}")
                else:
                    self.logger.warning(f"Failed to register webhook for {name}")
                    
            except Exception as e:
                self.logger.error(f"Error setting up webhook for {name}: {e}")
                results[name] = False
                
        return results
        
    def process_webhook_event(self, platform_name: str, payload: Dict[str, Any]) -> bool:
        """Process incoming webhook event"""
        
        try:
            if platform_name not in self.ci_configs:
                self.logger.warning(f"Unknown platform: {platform_name}")
                return False
                
            # Parse event based on platform
            ci_config = self.ci_configs[platform_name]
            trigger_config = self.trigger_configs[platform_name]
            
            event = self._parse_webhook_payload(ci_config.platform, payload)
            if not event:
                return False
                
            # Check if event should trigger tests
            if self._should_trigger_tests(event, trigger_config):
                self._queue_test_execution(platform_name, event)
                return True
                
            return False
            
        except Exception as e:
            self.logger.error(f"Error processing webhook event: {e}")
            return False
            
    def _parse_webhook_payload(self, platform: CIPlatform, 
                              payload: Dict[str, Any]) -> Optional[CIEvent]:
        """Parse webhook payload based on platform"""
        
        try:
            if platform == CIPlatform.GITHUB_ACTIONS:
                return self._parse_github_payload(payload)
            elif platform == CIPlatform.GITLAB_CI:
                return self._parse_gitlab_payload(payload)
            elif platform == CIPlatform.JENKINS:
                return self._parse_jenkins_payload(payload)
            else:
                self.logger.warning(f"Payload parsing not implemented for {platform}")
                return None
                
        except Exception as e:
            self.logger.error(f"Error parsing webhook payload: {e}")
            return None
            
    def _parse_github_payload(self, payload: Dict[str, Any]) -> Optional[CIEvent]:
        """Parse GitHub webhook payload"""
        
        if 'commits' in payload and payload['commits']:
            # Push event
            commit = payload['commits'][0]
            return CIEvent(
                event_type=TriggerEvent.COMMIT,
                repository=payload['repository']['full_name'],
                branch=payload['ref'].split('/')[-1],
                commit_hash=commit['id'],
                commit_message=commit['message'],
                author=commit['author']['name'],
                timestamp=datetime.fromisoformat(commit['timestamp'].replace('Z', '+00:00')),
                changed_files=[f['filename'] for f in payload.get('commits', [{}])[0].get('modified', [])]
            )
        elif 'pull_request' in payload:
            # Pull request event
            pr = payload['pull_request']
            return CIEvent(
                event_type=TriggerEvent.PULL_REQUEST,
                repository=payload['repository']['full_name'],
                branch=pr['head']['ref'],
                commit_hash=pr['head']['sha'],
                commit_message=pr['title'],
                author=pr['user']['login'],
                timestamp=datetime.fromisoformat(pr['created_at'].replace('Z', '+00:00')),
                pull_request_id=str(pr['number'])
            )
        elif 'release' in payload:
            # Release event
            release = payload['release']
            return CIEvent(
                event_type=TriggerEvent.RELEASE,
                repository=payload['repository']['full_name'],
                branch=release.get('target_commitish', 'main'),
                commit_hash=release.get('tag_name', ''),
                commit_message=release['name'],
                author=release['author']['login'],
                timestamp=datetime.fromisoformat(release['created_at'].replace('Z', '+00:00'))
            )
            
        return None
        
    def _parse_gitlab_payload(self, payload: Dict[str, Any]) -> Optional[CIEvent]:
        """Parse GitLab webhook payload"""
        
        if payload.get('object_kind') == 'push':
            return CIEvent(
                event_type=TriggerEvent.COMMIT,
                repository=payload['project']['path_with_namespace'],
                branch=payload['ref'].split('/')[-1],
                commit_hash=payload['after'],
                commit_message=payload['commits'][0]['message'] if payload['commits'] else '',
                author=payload['user_name'],
                timestamp=datetime.fromisoformat(payload['commits'][0]['timestamp']) if payload['commits'] else datetime.now()
            )
        elif payload.get('object_kind') == 'merge_request':
            mr = payload['object_attributes']
            return CIEvent(
                event_type=TriggerEvent.MERGE_REQUEST,
                repository=payload['project']['path_with_namespace'],
                branch=mr['source_branch'],
                commit_hash=mr['last_commit']['id'],
                commit_message=mr['title'],
                author=mr['author']['name'],
                timestamp=datetime.fromisoformat(mr['created_at']),
                pull_request_id=str(mr['iid'])
            )
            
        return None
        
    def _parse_jenkins_payload(self, payload: Dict[str, Any]) -> Optional[CIEvent]:
        """Parse Jenkins webhook payload"""
        
        # Jenkins payload parsing would depend on the specific webhook format
        return CIEvent(
            event_type=TriggerEvent.MANUAL,
            repository=payload.get('repository', 'unknown'),
            branch=payload.get('branch', 'main'),
            commit_hash=payload.get('commit', ''),
            commit_message=payload.get('message', ''),
            author=payload.get('author', 'jenkins'),
            timestamp=datetime.now()
        )
        
    def _should_trigger_tests(self, event: CIEvent, trigger_config: TriggerConfig) -> bool:
        """Determine if event should trigger tests"""
        
        # Check if event type is configured
        if event.event_type not in trigger_config.trigger_events:
            return False
            
        # Check branch filters
        if trigger_config.branch_filters and event.branch not in trigger_config.branch_filters:
            return False
            
        # Check skip CI patterns
        for pattern in trigger_config.skip_ci_patterns:
            if pattern.lower() in event.commit_message.lower():
                self.logger.info(f"Skipping CI due to pattern: {pattern}")
                return False
                
        # Check path filters (if specified)
        if (trigger_config.path_filters and event.changed_files and 
            not any(any(path_filter in file for path_filter in trigger_config.path_filters) 
                   for file in event.changed_files)):
            return False
            
        return True
        
    def _queue_test_execution(self, platform_name: str, event: CIEvent):
        """Queue test execution for an event"""
        
        self.event_queue.append((platform_name, event))
        
        # Start processing thread if not running
        if not self.processing_thread or not self.processing_thread.is_alive():
            self.processing_thread = threading.Thread(target=self._process_event_queue, daemon=True)
            self.processing_thread.start()
            
    def _process_event_queue(self):
        """Process queued CI events"""
        
        while not self.shutdown_event.is_set() and self.event_queue:
            try:
                platform_name, event = self.event_queue.pop(0)
                self._execute_tests_for_event(platform_name, event)
            except Exception as e:
                self.logger.error(f"Error processing event queue: {e}")
                
            time.sleep(1)  # Brief pause between processing
            
    def _execute_tests_for_event(self, platform_name: str, event: CIEvent):
        """Execute tests for a CI event"""
        
        try:
            ci_config = self.ci_configs[platform_name]
            trigger_config = self.trigger_configs[platform_name]
            
            # Update commit status to pending
            adapter = self.adapters[ci_config.platform]
            adapter.update_status(
                ci_config, event.commit_hash, TestResult.PENDING,
                "VIP tests started"
            )
            
            # Determine test suite and regression type
            suite_id = trigger_config.test_suite_mapping.get(event.event_type.value, 1)
            regression_type = trigger_config.regression_type_mapping.get(
                event.event_type.value, RegressionType.SMOKE
            )
            
            # Create regression configuration
            regression_config = RegressionConfig(
                name=f"CI_{event.event_type.value}_{event.commit_hash[:8]}",
                suite_id=suite_id,
                config_id=1,  # Default configuration
                regression_type=regression_type,
                git_commit_hash=event.commit_hash,
                git_branch=event.branch,
                notification_emails=[],
                max_parallel_tests=4,
                timeout_hours=2
            )
            
            # Start regression
            regression_id = self.regression_manager.schedule_regression(regression_config)
            
            # Monitor regression progress
            self._monitor_regression(platform_name, event, regression_id)
            
        except Exception as e:
            self.logger.error(f"Error executing tests for event: {e}")
            
            # Update status to error
            adapter = self.adapters[ci_config.platform]
            adapter.update_status(
                ci_config, event.commit_hash, TestResult.ERROR,
                f"Test execution failed: {str(e)}"
            )
            
    def _monitor_regression(self, platform_name: str, event: CIEvent, regression_id: int):
        """Monitor regression progress and update CI status"""
        
        def monitor_thread():
            ci_config = self.ci_configs[platform_name]
            adapter = self.adapters[ci_config.platform]
            
            start_time = datetime.now()
            timeout = timedelta(minutes=ci_config.timeout_minutes)
            
            while datetime.now() - start_time < timeout:
                try:
                    regression_run = self.regression_manager.get_regression_status(regression_id)
                    
                    if regression_run is None:
                        break
                        
                    if regression_run.status == "COMPLETED":
                        # Calculate results
                        pass_rate = (regression_run.passed_tests / regression_run.total_tests * 100 
                                   if regression_run.total_tests > 0 else 0)
                        
                        if regression_run.failed_tests == 0:
                            status = TestResult.SUCCESS
                            description = (f"All tests passed ({regression_run.passed_tests}/"
                                         f"{regression_run.total_tests}), "
                                         f"Coverage: {regression_run.current_coverage:.1f}%")
                        else:
                            status = TestResult.FAILURE
                            description = (f"Tests failed ({regression_run.failed_tests}/"
                                         f"{regression_run.total_tests}), "
                                         f"Pass rate: {pass_rate:.1f}%")
                            
                        adapter.update_status(ci_config, event.commit_hash, status, description)
                        
                        # Post detailed comment if PR/MR
                        if event.pull_request_id:
                            comment = self._generate_test_report_comment(regression_run)
                            adapter.post_comment(ci_config, event.pull_request_id, comment)
                            
                        break
                        
                    elif regression_run.status in ["FAILED", "STOPPED"]:
                        adapter.update_status(
                            ci_config, event.commit_hash, TestResult.FAILURE,
                            f"Regression {regression_run.status.lower()}"
                        )
                        break
                        
                    time.sleep(30)  # Check every 30 seconds
                    
                except Exception as e:
                    self.logger.error(f"Error monitoring regression: {e}")
                    break
                    
            # Timeout handling
            if datetime.now() - start_time >= timeout:
                adapter.update_status(
                    ci_config, event.commit_hash, TestResult.ERROR,
                    "Test execution timed out"
                )
                
        # Start monitoring in separate thread
        monitor_thread_instance = threading.Thread(target=monitor_thread, daemon=True)
        monitor_thread_instance.start()
        
    def _generate_test_report_comment(self, regression_run) -> str:
        """Generate test report comment for PR/MR"""
        
        pass_rate = (regression_run.passed_tests / regression_run.total_tests * 100 
                    if regression_run.total_tests > 0 else 0)
        
        status_emoji = "✅" if regression_run.failed_tests == 0 else "❌"
        
        comment = f"""
{status_emoji} **VIP Test Results**

| Metric | Value |
|--------|-------|
| **Total Tests** | {regression_run.total_tests} |
| **Passed** | {regression_run.passed_tests} |
| **Failed** | {regression_run.failed_tests} |
| **Pass Rate** | {pass_rate:.1f}% |
| **Coverage** | {regression_run.current_coverage:.1f}% |
| **Duration** | {datetime.now() - regression_run.start_time} |

**Regression Type:** {regression_run.config.regression_type.value}
**Test Suite:** {regression_run.config.name}
        """
        
        if regression_run.failed_tests > 0:
            comment += "\n⚠️ **Some tests failed.** Please review the test results and fix any issues."
        else:
            comment += "\n🎉 **All tests passed!** Great job!"
            
        return comment.strip()
        
    def create_status_check_config(self, platform_name: str, 
                                 required_checks: List[str] = None) -> Dict[str, Any]:
        """Create status check configuration for branch protection"""
        
        if required_checks is None:
            required_checks = ["vip-tests"]
            
        config = {
            "required_status_checks": {
                "strict": True,
                "contexts": required_checks
            },
            "enforce_admins": True,
            "required_pull_request_reviews": {
                "required_approving_review_count": 1,
                "dismiss_stale_reviews": True
            },
            "restrictions": None
        }
        
        return config
        
    def generate_ci_pipeline_config(self, platform: CIPlatform, 
                                  config_options: Dict[str, Any] = None) -> str:
        """Generate CI pipeline configuration file"""
        
        if config_options is None:
            config_options = {}
            
        if platform == CIPlatform.GITHUB_ACTIONS:
            return self._generate_github_actions_config(config_options)
        elif platform == CIPlatform.GITLAB_CI:
            return self._generate_gitlab_ci_config(config_options)
        elif platform == CIPlatform.JENKINS:
            return self._generate_jenkins_config(config_options)
        else:
            raise ValueError(f"Unsupported platform: {platform}")
            
    def _generate_github_actions_config(self, options: Dict[str, Any]) -> str:
        """Generate GitHub Actions workflow configuration"""
        
        config = {
            "name": "VIP Tests",
            "on": {
                "push": {
                    "branches": options.get("branches", ["main", "develop"])
                },
                "pull_request": {
                    "branches": options.get("branches", ["main", "develop"])
                }
            },
            "jobs": {
                "vip-tests": {
                    "runs-on": "ubuntu-latest",
                    "steps": [
                        {
                            "name": "Checkout code",
                            "uses": "actions/checkout@v3"
                        },
                        {
                            "name": "Setup Python",
                            "uses": "actions/setup-python@v4",
                            "with": {
                                "python-version": "3.8"
                            }
                        },
                        {
                            "name": "Install dependencies",
                            "run": "pip install -r requirements.txt"
                        },
                        {
                            "name": "Trigger VIP Tests",
                            "run": "python -m vip_cicd_integration trigger --platform github --event ${{ github.event_name }}"
                        }
                    ]
                }
            }
        }
        
        return yaml.dump(config, default_flow_style=False)
        
    def _generate_gitlab_ci_config(self, options: Dict[str, Any]) -> str:
        """Generate GitLab CI configuration"""
        
        config = {
            "stages": ["test"],
            "vip-tests": {
                "stage": "test",
                "image": "python:3.8",
                "before_script": [
                    "pip install -r requirements.txt"
                ],
                "script": [
                    "python -m vip_cicd_integration trigger --platform gitlab --event $CI_PIPELINE_SOURCE"
                ],
                "only": {
                    "refs": options.get("branches", ["main", "develop"])
                }
            }
        }
        
        return yaml.dump(config, default_flow_style=False)
        
    def _generate_jenkins_config(self, options: Dict[str, Any]) -> str:
        """Generate Jenkins pipeline configuration"""
        
        config = f"""
pipeline {{
    agent any
    
    triggers {{
        pollSCM('H/5 * * * *')
    }}
    
    stages {{
        stage('Checkout') {{
            steps {{
                checkout scm
            }}
        }}
        
        stage('Setup') {{
            steps {{
                sh 'pip install -r requirements.txt'
            }}
        }}
        
        stage('VIP Tests') {{
            steps {{
                sh 'python -m vip_cicd_integration trigger --platform jenkins --event ${{env.BUILD_CAUSE}}'
            }}
        }}
    }}
    
    post {{
        always {{
            publishHTML([
                allowMissing: false,
                alwaysLinkToLastBuild: true,
                keepAll: true,
                reportDir: 'reports',
                reportFiles: 'index.html',
                reportName: 'VIP Test Report'
            ])
        }}
    }}
}}
        """
        
        return config.strip()
        
    def add_result_callback(self, callback: Callable[[str, CIEvent, Any], None]):
        """Add callback for test result notifications"""
        self.result_callbacks.append(callback)
        
    def shutdown(self):
        """Shutdown the CI/CD integration system"""
        self.logger.info("Shutting down CI/CD integration...")
        
        self.shutdown_event.set()
        
        if self.processing_thread:
            self.processing_thread.join(timeout=10)
            
        self.logger.info("CI/CD integration shutdown complete")

def example_cicd_setup():
    """Example of setting up CI/CD integration"""
    
    # Initialize components
    db_manager = VIPTestConfigManager()
    execution_framework = VIPTestExecutionFramework()
    regression_manager = VIPRegressionManager(db_manager, execution_framework)
    cicd_integration = VIPCICDIntegration(db_manager, execution_framework, regression_manager)
    
    # GitHub configuration
    github_config = CIConfig(
        platform=CIPlatform.GITHUB_ACTIONS,
        server_url="https://api.github.com",
        auth_token="ghp_xxxxxxxxxxxxxxxxxxxx",
        project_id="owner/repository",
        webhook_secret="webhook_secret",
        timeout_minutes=60
    )
    
    github_trigger = TriggerConfig(
        trigger_events=[TriggerEvent.COMMIT, TriggerEvent.PULL_REQUEST],
        test_suite_mapping={
            "commit": 1,
            "pull_request": 1
        },
        regression_type_mapping={
            "commit": RegressionType.SMOKE,
            "pull_request": RegressionType.SANITY
        },
        branch_filters=["main", "develop"]
    )
    
    # Register platform
    success = cicd_integration.register_ci_platform("github", github_config, github_trigger)
    print(f"GitHub registration: {'Success' if success else 'Failed'}")
    
    # Setup webhooks
    webhook_results = cicd_integration.setup_webhooks("https://vip-server.company.com")
    print(f"Webhook setup results: {webhook_results}")
    
    # Generate pipeline configuration
    pipeline_config = cicd_integration.generate_ci_pipeline_config(
        CIPlatform.GITHUB_ACTIONS,
        {"branches": ["main", "develop", "feature/*"]}
    )
    print(f"Generated pipeline configuration:\n{pipeline_config}")

if __name__ == "__main__":
    example_cicd_setup()