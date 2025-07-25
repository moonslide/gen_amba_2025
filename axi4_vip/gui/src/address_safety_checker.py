#!/usr/bin/env python3
"""
Address Safety Checker for AMBA Bus Matrix
Validates address space configuration for security risks
"""

from typing import List, Tuple, Dict, Set
from dataclasses import dataclass
import logging

@dataclass
class AddressRange:
    """Represents an address range with metadata"""
    name: str
    base: int
    size: int  # in bytes
    secure_only: bool = False
    privileged_only: bool = False
    allowed_masters: List[str] = None
    
    @property
    def end(self) -> int:
        return self.base + self.size - 1
        
    def __post_init__(self):
        if self.allowed_masters is None:
            self.allowed_masters = []

@dataclass 
class SecurityViolation:
    """Security or safety violation detected"""
    severity: str  # CRITICAL, HIGH, MEDIUM, LOW
    category: str  # OVERLAP, HOLE, SECURITY, QOS, etc.
    message: str
    affected_components: List[str]
    recommendation: str

class AddressSafetyChecker:
    """Comprehensive address space safety validator"""
    
    def __init__(self):
        self.violations = []
        self.warnings = []
        
    def validate_configuration(self, slaves: List, masters: List = None) -> Tuple[bool, List[SecurityViolation]]:
        """
        Validate complete bus configuration for safety risks
        Returns: (is_safe, violations_list)
        """
        self.violations.clear()
        self.warnings.clear()
        
        # Convert to AddressRange objects
        address_ranges = []
        for slave in slaves:
            addr_range = AddressRange(
                name=slave.name,
                base=slave.base_address,
                size=slave.size * 1024,  # Convert KB to bytes
                secure_only=getattr(slave, 'secure_only', False),
                privileged_only=getattr(slave, 'privileged_only', False),
                allowed_masters=getattr(slave, 'allowed_masters', [])
            )
            address_ranges.append(addr_range)
        
        # Run all safety checks
        self._check_address_overlaps(address_ranges)
        self._check_address_holes(address_ranges)
        self._check_alignment_requirements(address_ranges)
        self._check_4kb_boundaries(address_ranges)
        self._check_security_consistency(address_ranges, masters or [])
        self._check_address_space_limits(address_ranges)
        
        # Classify severity
        critical_violations = [v for v in self.violations if v.severity == "CRITICAL"]
        
        return len(critical_violations) == 0, self.violations
    
    def _check_address_overlaps(self, ranges: List[AddressRange]):
        """Check for overlapping address ranges - CRITICAL RISK"""
        for i, range1 in enumerate(ranges):
            for j, range2 in enumerate(ranges[i+1:], i+1):
                if self._ranges_overlap(range1, range2):
                    self.violations.append(SecurityViolation(
                        severity="CRITICAL",
                        category="OVERLAP",
                        message=f"Address overlap detected: {range1.name} (0x{range1.base:X}-0x{range1.end:X}) "
                               f"overlaps with {range2.name} (0x{range2.base:X}-0x{range2.end:X})",
                        affected_components=[range1.name, range2.name],
                        recommendation="Adjust base addresses to eliminate overlap. "
                                     "Use address calculator to find safe ranges."
                    ))
    
    def _check_address_holes(self, ranges: List[AddressRange]):
        """Check for dangerous address holes"""
        # Sort ranges by base address
        sorted_ranges = sorted(ranges, key=lambda r: r.base)
        
        for i in range(len(sorted_ranges) - 1):
            current = sorted_ranges[i]
            next_range = sorted_ranges[i + 1]
            
            hole_start = current.end + 1
            hole_end = next_range.base - 1
            
            if hole_end >= hole_start:
                hole_size = hole_end - hole_start + 1
                if hole_size > 1024 * 1024:  # Large holes (>1MB) are risky
                    self.violations.append(SecurityViolation(
                        severity="HIGH",
                        category="HOLE",
                        message=f"Large address hole detected: 0x{hole_start:X}-0x{hole_end:X} "
                               f"({hole_size} bytes). Unmapped accesses will hang the bus.",
                        affected_components=[current.name, next_range.name],
                        recommendation="Add default error slave or ensure masters never access this range."
                    ))
    
    def _check_alignment_requirements(self, ranges: List[AddressRange]):
        """Check address alignment requirements"""
        for range_obj in ranges:
            # Check base address alignment
            if range_obj.size >= 1024 and range_obj.base % 1024 != 0:
                self.violations.append(SecurityViolation(
                    severity="MEDIUM",
                    category="ALIGNMENT", 
                    message=f"{range_obj.name}: Base address 0x{range_obj.base:X} not aligned to size boundary",
                    affected_components=[range_obj.name],
                    recommendation="Align base address to size boundary for optimal performance."
                ))
            
            # Check power-of-2 size alignment  
            if range_obj.size > 0 and (range_obj.size & (range_obj.size - 1)) != 0:
                self.violations.append(SecurityViolation(
                    severity="LOW",
                    category="ALIGNMENT",
                    message=f"{range_obj.name}: Size {range_obj.size} bytes is not power-of-2",
                    affected_components=[range_obj.name],
                    recommendation="Use power-of-2 sizes for simpler address decoding."
                ))
    
    def _check_4kb_boundaries(self, ranges: List[AddressRange]):
        """Check for 4KB boundary violations (AXI4 spec requirement)"""
        for range_obj in ranges:
            # Check if range crosses 4KB boundaries inappropriately
            start_page = range_obj.base >> 12  # 4KB pages
            end_page = range_obj.end >> 12
            
            if end_page > start_page and range_obj.size < 4096:
                self.violations.append(SecurityViolation(
                    severity="HIGH",
                    category="4KB_BOUNDARY",
                    message=f"{range_obj.name}: Small range crosses 4KB boundary - "
                           f"may violate AXI4 burst requirements",
                    affected_components=[range_obj.name],
                    recommendation="Align to 4KB boundary or ensure burst lengths respect boundaries."
                ))
    
    def _check_security_consistency(self, ranges: List[AddressRange], masters: List):
        """Check security attribute consistency"""
        secure_ranges = [r for r in ranges if r.secure_only]
        privileged_ranges = [r for r in ranges if r.privileged_only]
        
        # Check for secure ranges adjacent to non-secure (potential attack vector)
        for secure_range in secure_ranges:
            for other_range in ranges:
                if other_range.name != secure_range.name and not other_range.secure_only:
                    if self._ranges_adjacent(secure_range, other_range):
                        self.violations.append(SecurityViolation(
                            severity="HIGH",
                            category="SECURITY",
                            message=f"Secure region {secure_range.name} adjacent to non-secure "
                                   f"{other_range.name} - potential security risk",
                            affected_components=[secure_range.name, other_range.name],
                            recommendation="Add buffer/guard regions between secure and non-secure areas."
                        ))
        
        # Check for overly permissive access
        for range_obj in ranges:
            if not range_obj.allowed_masters:  # Empty = all allowed
                if range_obj.secure_only or range_obj.privileged_only:
                    self.violations.append(SecurityViolation(
                        severity="HIGH", 
                        category="SECURITY",
                        message=f"{range_obj.name}: Secure/privileged region allows all masters - "
                               "overly permissive",
                        affected_components=[range_obj.name],
                        recommendation="Explicitly specify which masters can access secure regions."
                    ))
    
    def _check_address_space_limits(self, ranges: List[AddressRange]):
        """Check for address space overflow"""
        max_addr = max(r.end for r in ranges) if ranges else 0
        
        # Check 32-bit address space limits
        if max_addr >= (1 << 32):
            self.violations.append(SecurityViolation(
                severity="CRITICAL",
                category="OVERFLOW", 
                message=f"Address space exceeds 32-bit limit: max address = 0x{max_addr:X}",
                affected_components=[r.name for r in ranges if r.end >= (1 << 32)],
                recommendation="Reduce address ranges or use 64-bit addressing."
            ))
        
        # Warn about high memory usage
        total_size = sum(r.size for r in ranges)
        if total_size > 1024 * 1024 * 1024:  # > 1GB
            self.violations.append(SecurityViolation(
                severity="LOW",
                category="RESOURCE",
                message=f"Large total address space: {total_size // (1024*1024)}MB",
                affected_components=[r.name for r in ranges],
                recommendation="Consider if all address space is necessary."
            ))
    
    def _ranges_overlap(self, r1: AddressRange, r2: AddressRange) -> bool:
        """Check if two address ranges overlap"""
        return not (r1.end < r2.base or r2.end < r1.base)
    
    def _ranges_adjacent(self, r1: AddressRange, r2: AddressRange) -> bool:
        """Check if two address ranges are adjacent (within 4KB)"""
        gap = min(abs(r1.base - r2.end - 1), abs(r2.base - r1.end - 1))
        return gap < 4096  # Adjacent if within 4KB
    
    def generate_safety_report(self) -> str:
        """Generate human-readable safety report"""
        if not self.violations:
            return "✅ Address space configuration is SAFE - no violations detected."
        
        report = []
        report.append("🚨 ADDRESS SPACE SAFETY REPORT")  
        report.append("=" * 40)
        
        # Group by severity
        critical = [v for v in self.violations if v.severity == "CRITICAL"]
        high = [v for v in self.violations if v.severity == "HIGH"] 
        medium = [v for v in self.violations if v.severity == "MEDIUM"]
        low = [v for v in self.violations if v.severity == "LOW"]
        
        if critical:
            report.append(f"\n🔴 CRITICAL ISSUES ({len(critical)}):")
            for v in critical:
                report.append(f"   • {v.message}")
                report.append(f"     → {v.recommendation}")
        
        if high:
            report.append(f"\n🟡 HIGH PRIORITY ({len(high)}):")
            for v in high:
                report.append(f"   • {v.message}")
        
        if medium:
            report.append(f"\n🟠 MEDIUM PRIORITY ({len(medium)}):")
            for v in medium:
                report.append(f"   • {v.message}")
                
        if low:
            report.append(f"\n🟢 LOW PRIORITY ({len(low)}):")
            for v in low:
                report.append(f"   • {v.message}")
        
        report.append(f"\n📊 SUMMARY: {len(self.violations)} total issues")
        report.append(f"   • {len(critical)} critical, {len(high)} high, {len(medium)} medium, {len(low)} low")
        
        if critical:
            report.append("\n⚠️  CRITICAL ISSUES MUST BE RESOLVED BEFORE DEPLOYMENT")
        
        return "\n".join(report)

def validate_bus_configuration(slaves, masters=None):
    """Convenience function for configuration validation"""
    checker = AddressSafetyChecker()
    is_safe, violations = checker.validate_configuration(slaves, masters)
    report = checker.generate_safety_report()
    return is_safe, violations, report