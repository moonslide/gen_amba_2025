#!/usr/bin/env python3
"""Read AXI4 specification to understand arbiter requirements"""

import PyPDF2
import re

def read_axi_spec():
    """Read AXI4 specification PDF and extract arbiter information"""
    pdf_path = '/home/timtim01/eda_test/project/gen_amba_2025/IHI0022D_amba_axi_protocol_spec.pdf'
    
    try:
        with open(pdf_path, 'rb') as file:
            pdf_reader = PyPDF2.PdfReader(file)
            
            print(f"Total pages: {len(pdf_reader.pages)}")
            
            # Search for arbiter-related content
            arbiter_info = []
            interconnect_info = []
            
            for page_num, page in enumerate(pdf_reader.pages):
                try:
                    text = page.extract_text()
                    
                    # Look for arbiter-related sections
                    if any(keyword in text.lower() for keyword in ['arbiter', 'arbitration']):
                        arbiter_info.append({
                            'page': page_num + 1,
                            'content': text[:500] + '...' if len(text) > 500 else text
                        })
                    
                    # Look for interconnect sections
                    if any(keyword in text.lower() for keyword in ['interconnect', 'crossbar', 'multi-master']):
                        interconnect_info.append({
                            'page': page_num + 1,
                            'content': text[:500] + '...' if len(text) > 500 else text
                        })
                        
                except Exception as e:
                    print(f"Error reading page {page_num + 1}: {e}")
                    continue
            
            # Print relevant sections
            print("\n=== ARBITER SECTIONS ===")
            for info in arbiter_info[:5]:  # First 5 matches
                print(f"Page {info['page']}:")
                print(info['content'])
                print("-" * 80)
            
            print("\n=== INTERCONNECT SECTIONS ===")  
            for info in interconnect_info[:5]:  # First 5 matches
                print(f"Page {info['page']}:")
                print(info['content'])
                print("-" * 80)
                
            # Look for specific sections about master/slave counts
            print("\n=== SEARCHING FOR SCALABILITY INFO ===")
            for page_num, page in enumerate(pdf_reader.pages):
                try:
                    text = page.extract_text()
                    
                    # Look for mentions of master/slave numbers
                    if re.search(r'(master|slave).*\d+', text.lower()) or 'scalable' in text.lower():
                        print(f"Page {page_num + 1}: Found scalability info")
                        # Extract sentences with numbers
                        sentences = text.split('.')
                        for sentence in sentences:
                            if any(keyword in sentence.lower() for keyword in ['master', 'slave', 'scalable']) and any(char.isdigit() for char in sentence):
                                print(f"  - {sentence.strip()}")
                        print()
                        
                except Exception as e:
                    continue
                    
    except FileNotFoundError:
        print(f"PDF file not found at {pdf_path}")
    except Exception as e:
        print(f"Error reading PDF: {e}")

if __name__ == "__main__":
    read_axi_spec()