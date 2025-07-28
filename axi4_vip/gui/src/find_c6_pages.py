#!/usr/bin/env python3
"""Find the actual page numbers for Chapter C6"""

import PyPDF2

def find_c6_pages():
    """Find the actual page numbers for Chapter C6"""
    pdf_path = '/home/timtim01/eda_test/project/gen_amba_2025/IHI0022D_amba_axi_protocol_spec.pdf'
    
    try:
        with open(pdf_path, 'rb') as file:
            pdf_reader = PyPDF2.PdfReader(file)
            
            # Search for C6.1, C6.2, etc. 
            c6_pages = []
            
            for page_num, page in enumerate(pdf_reader.pages):
                try:
                    text = page.extract_text()
                    
                    # Look for C6 section headers
                    if any(section in text for section in ['C6.1', 'C6.2', 'C6.3', 'C6.4', 'C6.5', 'C6.6', 'C6.7']):
                        c6_pages.append(page_num)
                        print(f"Found C6 content on page {page_num + 1}")
                        
                        # Print the section headers found
                        lines = text.split('\n')
                        for line in lines:
                            if any(section in line for section in ['C6.1', 'C6.2', 'C6.3', 'C6.4', 'C6.5', 'C6.6', 'C6.7']):
                                print(f"  Section: {line.strip()}")
                        print()
                        
                except Exception as e:
                    continue
            
            # Now read the actual C6 pages
            if c6_pages:
                print("=== READING C6 CONTENT ===")
                for page_num in sorted(set(c6_pages)):
                    try:
                        text = pdf_reader.pages[page_num].extract_text()
                        print(f"\n=== PAGE {page_num + 1} ===")
                        print(text)
                        print("=" * 80)
                    except Exception as e:
                        continue
            
            # Also search for pages mentioning arbitration
            print("\n=== PAGES WITH ARBITRATION CONTENT ===")
            for page_num, page in enumerate(pdf_reader.pages):
                try:
                    text = page.extract_text()
                    if 'arbitrat' in text.lower():
                        print(f"\nPage {page_num + 1} mentions arbitration:")
                        lines = text.split('\n')
                        for line in lines:
                            if 'arbitrat' in line.lower():
                                print(f"  {line.strip()}")
                except Exception as e:
                    continue
                    
    except Exception as e:
        print(f"Error: {e}")

if __name__ == "__main__":
    find_c6_pages()