#!/usr/bin/env python3
"""Extract specific arbiter requirements from AXI4 specification"""

import PyPDF2
import re

def extract_arbiter_requirements():
    """Extract detailed arbiter requirements from AXI4 spec"""
    pdf_path = '/home/timtim01/eda_test/project/gen_amba_2025/IHI0022D_amba_axi_protocol_spec.pdf'
    
    arbiter_keywords = ['arbiter', 'arbitration', 'priority', 'grant', 'request', 'round-robin', 'fairness']
    interconnect_keywords = ['interconnect', 'crossbar', 'switch', 'fabric', 'multi-master', 'multi-slave']
    
    try:
        with open(pdf_path, 'rb') as file:
            pdf_reader = PyPDF2.PdfReader(file)
            
            # Find the interconnect chapter (likely Chapter C6)
            interconnect_pages = []
            
            for page_num, page in enumerate(pdf_reader.pages):
                try:
                    text = page.extract_text()
                    
                    # Look for the interconnect requirements chapter
                    if 'C6 Interconnect Requirements' in text or 'Interconnect Requirements' in text:
                        print(f"Found Interconnect Requirements on page {page_num + 1}")
                        print("=" * 80)
                        print(text)
                        print("=" * 80)
                        interconnect_pages.append(page_num)
                    
                    # Look for specific arbiter mentions
                    if any(keyword in text.lower() for keyword in arbiter_keywords):
                        lines = text.split('\n')
                        for i, line in enumerate(lines):
                            if any(keyword in line.lower() for keyword in arbiter_keywords):
                                # Print context around the match
                                start = max(0, i-2)
                                end = min(len(lines), i+3)
                                context = '\n'.join(lines[start:end])
                                print(f"\nPage {page_num + 1} - Arbiter context:")
                                print(context)
                                print("-" * 50)
                                
                except Exception as e:
                    continue
            
            # Focus on interconnect pages and nearby pages
            if interconnect_pages:
                print(f"\n=== DETAILED INTERCONNECT ANALYSIS ===")
                for base_page in interconnect_pages:
                    # Read 5 pages around each interconnect mention
                    for offset in range(-2, 8):
                        page_idx = base_page + offset
                        if 0 <= page_idx < len(pdf_reader.pages):
                            try:
                                text = pdf_reader.pages[page_idx].extract_text()
                                
                                # Look for specific implementation details
                                if any(keyword in text.lower() for keyword in ['priority', 'arbitration', 'qos', 'ordering']):
                                    print(f"\nPage {page_idx + 1}:")
                                    
                                    # Extract relevant paragraphs
                                    paragraphs = text.split('\n\n')
                                    for para in paragraphs:
                                        if any(keyword in para.lower() for keyword in ['priority', 'arbitration', 'qos', 'ordering', 'master', 'slave']):
                                            print(f"  {para.strip()}")
                                    print("-" * 60)
                                    
                            except Exception as e:
                                continue
            
    except Exception as e:
        print(f"Error: {e}")

if __name__ == "__main__":
    extract_arbiter_requirements()