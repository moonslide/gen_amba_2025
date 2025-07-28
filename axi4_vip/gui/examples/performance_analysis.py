#!/usr/bin/env python3
"""
Example: Performance analysis and optimization of bus configurations
Demonstrates bandwidth calculations, latency analysis, and optimization strategies
"""

import sys
import os
import json
import math
sys.path.append(os.path.join(os.path.dirname(__file__), '..', 'src'))

from bus_config import BusConfig, Master, Slave

class PerformanceAnalyzer:
    """Analyze and optimize bus performance"""
    
    def __init__(self, config):
        self.config = config
        self.clock_freq_mhz = 1000  # 1GHz default
        
    def calculate_bandwidth(self):
        """Calculate theoretical bandwidth for each master and total"""
        results = {
            "clock_freq_mhz": self.clock_freq_mhz,
            "data_width_bytes": self.config.data_width // 8,
            "masters": {},
            "slaves": {},
            "total": {}
        }
        
        # Per-master bandwidth (assuming full utilization)
        for master in self.config.masters:
            # Outstanding transactions = 2^ID_WIDTH
            outstanding = 2 ** master.id_width
            
            # Bandwidth = data_width * frequency * utilization
            # Assume 80% utilization for calculation
            bandwidth_mbps = (self.config.data_width / 8) * self.clock_freq_mhz * 0.8
            
            results["masters"][master.name] = {
                "id_width": master.id_width,
                "max_outstanding": outstanding,
                "theoretical_bandwidth_mbps": bandwidth_mbps,
                "theoretical_bandwidth_gbps": bandwidth_mbps / 1000
            }
        
        # Per-slave bandwidth (limited by latency)
        for slave in self.config.slaves:
            # Effective bandwidth considering latency
            avg_latency = (slave.read_latency + slave.write_latency) / 2
            transactions_per_sec = self.clock_freq_mhz * 1e6 / avg_latency
            
            # Assume average burst length of 8
            avg_burst_length = 8
            bandwidth_mbps = (transactions_per_sec * avg_burst_length * 
                            self.config.data_width / 8) / 1e6
            
            results["slaves"][slave.name] = {
                "read_latency": slave.read_latency,
                "write_latency": slave.write_latency,
                "avg_latency": avg_latency,
                "effective_bandwidth_mbps": bandwidth_mbps,
                "effective_bandwidth_gbps": bandwidth_mbps / 1000
            }
        
        # Total system bandwidth
        total_master_bw = sum(m["theoretical_bandwidth_gbps"] 
                            for m in results["masters"].values())
        total_slave_bw = sum(s["effective_bandwidth_gbps"] 
                           for s in results["slaves"].values())
        
        results["total"] = {
            "aggregate_master_bandwidth_gbps": total_master_bw,
            "aggregate_slave_bandwidth_gbps": total_slave_bw,
            "bottleneck": "slaves" if total_slave_bw < total_master_bw else "masters",
            "utilization_percent": min(100, (total_slave_bw / total_master_bw * 100))
                                 if total_master_bw > 0 else 0
        }
        
        return results
    
    def analyze_latency(self):
        """Analyze transaction latency"""
        results = {
            "worst_case_latency": {},
            "average_latency": {},
            "qos_impact": {}
        }
        
        # Calculate worst-case latency for each master-slave pair
        for master in self.config.masters:
            master_latencies = {}
            
            for slave in self.config.slaves:
                # Base latency
                base_read = slave.read_latency
                base_write = slave.write_latency
                
                # Arbitration delay (depends on number of higher priority masters)
                higher_priority_masters = sum(1 for m in self.config.masters 
                                            if m.priority > master.priority)
                
                # Worst case: all higher priority masters are active
                arb_delay = higher_priority_masters * 10  # 10 cycles per master
                
                # QoS can reduce arbitration delay
                if master.qos_support and self.config.arbitration == "QOS":
                    arb_delay = arb_delay // 2
                
                worst_read = base_read + arb_delay
                worst_write = base_write + arb_delay
                
                master_latencies[slave.name] = {
                    "read": worst_read,
                    "write": worst_write,
                    "arbitration_penalty": arb_delay
                }
            
            results["worst_case_latency"][master.name] = master_latencies
        
        return results
    
    def identify_bottlenecks(self):
        """Identify system bottlenecks"""
        bottlenecks = []
        
        # Check for ID width limitations
        for master in self.config.masters:
            if master.id_width < 4:
                bottlenecks.append({
                    "type": "limited_outstanding",
                    "component": master.name,
                    "issue": f"Only {2**master.id_width} outstanding transactions",
                    "impact": "reduced_bandwidth",
                    "recommendation": "Increase ID width to at least 4"
                })
        
        # Check for high latency slaves
        for slave in self.config.slaves:
            if slave.read_latency > 20 or slave.write_latency > 20:
                bottlenecks.append({
                    "type": "high_latency",
                    "component": slave.name,
                    "issue": f"High latency: R={slave.read_latency}, W={slave.write_latency}",
                    "impact": "reduced_throughput",
                    "recommendation": "Add caching or reduce slave latency"
                })
        
        # Check for narrow data width
        if self.config.data_width < 64:
            bottlenecks.append({
                "type": "narrow_bus",
                "component": "system",
                "issue": f"Data width only {self.config.data_width} bits",
                "impact": "limited_bandwidth",
                "recommendation": "Consider 64-bit or wider data bus"
            })
        
        # Check for arbitration issues
        if len(self.config.masters) > 4 and self.config.arbitration != "QOS":
            bottlenecks.append({
                "type": "arbitration",
                "component": "interconnect",
                "issue": "Many masters without QoS arbitration",
                "impact": "unpredictable_latency",
                "recommendation": "Enable QoS-based arbitration"
            })
        
        return bottlenecks
    
    def suggest_optimizations(self):
        """Suggest optimizations based on analysis"""
        optimizations = []
        
        bandwidth = self.calculate_bandwidth()
        latency = self.analyze_latency()
        bottlenecks = self.identify_bottlenecks()
        
        # Bandwidth optimizations
        if bandwidth["total"]["utilization_percent"] < 50:
            optimizations.append({
                "category": "bandwidth",
                "priority": "high",
                "suggestion": "System is bandwidth limited",
                "actions": [
                    "Increase slave performance (reduce latency)",
                    "Add more slave ports for parallel access",
                    "Consider wider data bus"
                ]
            })
        
        # Latency optimizations
        max_latencies = []
        for master, slaves in latency["worst_case_latency"].items():
            for slave, lat in slaves.items():
                max_latencies.append(max(lat["read"], lat["write"]))
        
        if max(max_latencies) > 100:
            optimizations.append({
                "category": "latency", 
                "priority": "high",
                "suggestion": "High worst-case latency detected",
                "actions": [
                    "Implement QoS to prioritize critical masters",
                    "Add dedicated paths for low-latency traffic",
                    "Consider hierarchical bus structure"
                ]
            })
        
        # Outstanding transaction optimizations
        total_outstanding = sum(2**m.id_width for m in self.config.masters)
        if total_outstanding < len(self.config.masters) * 8:
            optimizations.append({
                "category": "concurrency",
                "priority": "medium",
                "suggestion": "Limited outstanding transaction capability",
                "actions": [
                    "Increase ID width for bandwidth-critical masters",
                    "Implement ID virtualization in interconnect",
                    "Consider AXI4 upgrade for 256 outstanding support"
                ]
            })
        
        return optimizations

def analyze_system_performance():
    """Perform comprehensive performance analysis"""
    
    # Create a realistic high-performance system
    config = BusConfig()
    config.bus_type = "AXI4"
    config.data_width = 128
    config.addr_width = 40
    config.arbitration = "QOS"
    
    # High-performance masters
    masters_config = [
        ("CPU_Cluster_0", 6, 15, True, True),    # High priority CPU
        ("CPU_Cluster_1", 6, 14, True, True),    # Second CPU cluster
        ("GPU", 8, 12, True, False),             # High bandwidth GPU
        ("DMA_0", 4, 8, True, False),            # DMA engine
        ("DMA_1", 4, 7, True, False),            # Second DMA
        ("PCIe", 6, 10, True, False),            # PCIe endpoint
        ("Video_Enc", 4, 9, True, False),        # Video encoder
        ("Video_Dec", 4, 9, True, False),        # Video decoder
    ]
    
    for name, id_width, priority, qos, excl in masters_config:
        master = Master(name)
        master.id_width = id_width
        master.priority = priority
        master.qos_support = qos
        master.exclusive_support = excl
        config.masters.append(master)
    
    # Memory hierarchy
    slaves_config = [
        ("DDR4_Ch0", 0x0000000000, 4194304, "Memory", 25, 15),      # 4GB DDR4
        ("DDR4_Ch1", 0x100000000, 4194304, "Memory", 25, 15),       # 4GB DDR4
        ("HBM", 0x200000000, 1048576, "Memory", 10, 8),             # 1GB HBM
        ("L3_Cache", 0x240000000, 32768, "Memory", 4, 3),           # 32MB L3
        ("SRAM", 0x242000000, 8192, "Memory", 2, 1),                # 8MB SRAM
        ("PCIe_Memory", 0x300000000, 262144, "Memory", 30, 30),     # 256MB PCIe
        ("Registers", 0x400000000, 1024, "Peripheral", 2, 2),       # 1MB registers
    ]
    
    for name, base, size, mem_type, r_lat, w_lat in slaves_config:
        slave = Slave(name, base, size)
        slave.memory_type = mem_type
        slave.read_latency = r_lat
        slave.write_latency = w_lat
        config.slaves.append(slave)
    
    # Perform analysis
    print("AMBA Bus Performance Analysis")
    print("="*70)
    
    analyzer = PerformanceAnalyzer(config)
    
    # 1. Bandwidth Analysis
    print("\n1. BANDWIDTH ANALYSIS")
    print("-"*50)
    bandwidth = analyzer.calculate_bandwidth()
    
    print(f"System Configuration:")
    print(f"  Clock: {bandwidth['clock_freq_mhz']} MHz")
    print(f"  Data Width: {config.data_width} bits ({bandwidth['data_width_bytes']} bytes)")
    print(f"  Masters: {len(config.masters)}")
    print(f"  Slaves: {len(config.slaves)}")
    
    print(f"\nMaster Bandwidth Capability:")
    for master, bw in bandwidth["masters"].items():
        print(f"  {master:<15} {bw['theoretical_bandwidth_gbps']:.1f} GB/s "
              f"(Outstanding: {bw['max_outstanding']})")
    
    print(f"\nSlave Bandwidth Capability:")
    for slave, bw in bandwidth["slaves"].items():
        print(f"  {slave:<15} {bw['effective_bandwidth_gbps']:.1f} GB/s "
              f"(Latency R/W: {bw['read_latency']}/{bw['write_latency']})")
    
    print(f"\nSystem Bandwidth Summary:")
    print(f"  Total Master Capability: {bandwidth['total']['aggregate_master_bandwidth_gbps']:.1f} GB/s")
    print(f"  Total Slave Capability: {bandwidth['total']['aggregate_slave_bandwidth_gbps']:.1f} GB/s")
    print(f"  Bottleneck: {bandwidth['total']['bottleneck'].upper()}")
    print(f"  Utilization: {bandwidth['total']['utilization_percent']:.1f}%")
    
    # 2. Latency Analysis
    print("\n2. LATENCY ANALYSIS")
    print("-"*50)
    latency = analyzer.analyze_latency()
    
    # Show worst case for critical masters
    critical_masters = ["CPU_Cluster_0", "GPU", "PCIe"]
    for master in critical_masters:
        if master in latency["worst_case_latency"]:
            print(f"\n{master} worst-case latency (cycles):")
            for slave, lat in latency["worst_case_latency"][master].items():
                if lat["arbitration_penalty"] > 0:
                    print(f"  {slave:<15} Read: {lat['read']:3d}, Write: {lat['write']:3d} "
                          f"(+{lat['arbitration_penalty']} arbitration)")
    
    # 3. Bottleneck Analysis
    print("\n3. BOTTLENECK ANALYSIS")  
    print("-"*50)
    bottlenecks = analyzer.identify_bottlenecks()
    
    if bottlenecks:
        for bottleneck in bottlenecks:
            print(f"\n{bottleneck['type'].upper()} in {bottleneck['component']}:")
            print(f"  Issue: {bottleneck['issue']}")
            print(f"  Impact: {bottleneck['impact']}")
            print(f"  Fix: {bottleneck['recommendation']}")
    else:
        print("No major bottlenecks identified!")
    
    # 4. Optimization Suggestions
    print("\n4. OPTIMIZATION RECOMMENDATIONS")
    print("-"*50)
    optimizations = analyzer.suggest_optimizations()
    
    for i, opt in enumerate(optimizations, 1):
        print(f"\n{i}. {opt['suggestion']} (Priority: {opt['priority'].upper()})")
        print("   Recommended actions:")
        for action in opt['actions']:
            print(f"   - {action}")
    
    # Save analysis report
    report = {
        "system_config": {
            "bus_type": config.bus_type,
            "data_width": config.data_width,
            "num_masters": len(config.masters),
            "num_slaves": len(config.slaves)
        },
        "bandwidth_analysis": bandwidth,
        "latency_analysis": {
            "critical_paths": {
                master: latency["worst_case_latency"].get(master, {})
                for master in critical_masters
            }
        },
        "bottlenecks": bottlenecks,
        "optimizations": optimizations
    }
    
    report_file = "performance_analysis_report.json"
    with open(report_file, 'w') as f:
        json.dump(report, f, indent=2)
    
    print(f"\n\nDetailed report saved to: {report_file}")
    
    return report

if __name__ == "__main__":
    analyze_system_performance()