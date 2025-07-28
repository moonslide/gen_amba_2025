#!/usr/bin/env python3
"""Extract Chapter C6 Interconnect Requirements from AXI specification"""

import PyPDF2

def get_c6_chapter():
    """Extract the complete Chapter C6 content"""
    pdf_path = '/home/timtim01/eda_test/project/gen_amba_2025/IHI0022D_amba_axi_protocol_spec.pdf'
    
    try:
        with open(pdf_path, 'rb') as file:
            pdf_reader = PyPDF2.PdfReader(file)
            
            c6_started = False
            c6_content = []
            
            for page_num, page in enumerate(pdf_reader.pages):
                try:
                    text = page.extract_text()
                    
                    # Start capturing when we find C6
                    if 'C6 Interconnect Requirements' in text and not c6_started:
                        c6_started = True
                        print(f"Found C6 start on page {page_num + 1}")
                    
                    # Stop when we find C7 or end of document
                    if c6_started and ('C7 Cache Maintenance' in text or 'Chapter C7' in text):
                        print(f"Found C6 end on page {page_num + 1}")
                        break
                    
                    if c6_started:
                        c6_content.append(f"\n=== PAGE {page_num + 1} ===\n{text}")
                        
                except Exception as e:
                    continue
            
            # Print all C6 content
            print("\n".join(c6_content))
            
            # Also look specifically for QoS and arbitration sections
            print("\n\n=== SEARCHING FOR QOS AND ARBITRATION ===")
            for page_num, page in enumerate(pdf_reader.pages):
                try:
                    text = page.extract_text()
                    if any(keyword in text.lower() for keyword in ['qos', 'quality of service', 'priority']):
                        print(f"\nPage {page_num + 1} - QoS/Priority content:")
                        paragraphs = text.split('\n')
                        for para in paragraphs:
                            if any(keyword in para.lower() for keyword in ['qos', 'quality', 'priority', 'arbitration']):
                                print(f"  {para.strip()}")
                        print("-" * 60)
                except Exception as e:
                    continue
                    
    except Exception as e:
        print(f"Error: {e}")

if __name__ == "__main__":
    get_c6_chapter()