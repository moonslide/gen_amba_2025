#!/bin/bash
# Script to convert Markdown documentation to PDF
# Requires: pandoc, wkhtmltopdf, or markdown-pdf

echo "GEN_AMBA Documentation Converter"
echo "================================"

INPUT="gen_amba_20251220.md"
OUTPUT_PDF="gen_amba_20251220.pdf"
OUTPUT_HTML="gen_amba_20251220.html"

# Check if input file exists
if [ ! -f "$INPUT" ]; then
    echo "Error: $INPUT not found!"
    exit 1
fi

# Method 1: Using pandoc (if available)
if command -v pandoc &> /dev/null; then
    echo "Converting with pandoc..."
    pandoc "$INPUT" \
        --pdf-engine=xelatex \
        --variable geometry:margin=1in \
        --variable fontsize=11pt \
        --variable documentclass=report \
        --toc \
        --number-sections \
        -o "$OUTPUT_PDF"
    
    if [ $? -eq 0 ]; then
        echo "✓ PDF created: $OUTPUT_PDF"
        exit 0
    fi
fi

# Method 2: Using markdown-pdf (if available)
if command -v markdown-pdf &> /dev/null; then
    echo "Converting with markdown-pdf..."
    markdown-pdf "$INPUT" -o "$OUTPUT_PDF"
    
    if [ $? -eq 0 ]; then
        echo "✓ PDF created: $OUTPUT_PDF"
        exit 0
    fi
fi

# Method 3: Convert to HTML first (fallback)
echo "Converting to HTML..."
if command -v pandoc &> /dev/null; then
    pandoc "$INPUT" -s --toc -o "$OUTPUT_HTML"
else
    # Basic markdown to HTML
    cat > "$OUTPUT_HTML" << 'EOF'
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>GEN_AMBA User Manual 2025</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 40px; }
        h1 { color: #333; border-bottom: 3px solid #333; }
        h2 { color: #555; border-bottom: 1px solid #ccc; }
        h3 { color: #666; }
        code { background: #f4f4f4; padding: 2px 4px; }
        pre { background: #f4f4f4; padding: 10px; overflow-x: auto; }
        table { border-collapse: collapse; width: 100%; }
        th, td { border: 1px solid #ddd; padding: 8px; text-align: left; }
        th { background: #f2f2f2; }
    </style>
</head>
<body>
EOF
    
    # Simple markdown to HTML conversion
    sed 's/^# \(.*\)/<h1>\1<\/h1>/g' "$INPUT" | \
    sed 's/^## \(.*\)/<h2>\1<\/h2>/g' | \
    sed 's/^### \(.*\)/<h3>\1<\/h3>/g' | \
    sed 's/^```.*/<pre>/g' | \
    sed 's/^```/<\/pre>/g' | \
    sed 's/`\([^`]*\)`/<code>\1<\/code>/g' | \
    sed 's/^\* \(.*\)/<li>\1<\/li>/g' | \
    sed 's/^\- \(.*\)/<li>\1<\/li>/g' >> "$OUTPUT_HTML"
    
    echo "</body></html>" >> "$OUTPUT_HTML"
fi

echo "✓ HTML created: $OUTPUT_HTML"

# Try to convert HTML to PDF using wkhtmltopdf
if command -v wkhtmltopdf &> /dev/null; then
    echo "Converting HTML to PDF with wkhtmltopdf..."
    wkhtmltopdf "$OUTPUT_HTML" "$OUTPUT_PDF"
    
    if [ $? -eq 0 ]; then
        echo "✓ PDF created: $OUTPUT_PDF"
        exit 0
    fi
fi

echo ""
echo "Manual conversion options:"
echo "1. Open $OUTPUT_HTML in a browser and print to PDF"
echo "2. Install pandoc: sudo apt-get install pandoc texlive-xetex"
echo "3. Install markdown-pdf: npm install -g markdown-pdf"
echo "4. Use online converter: https://www.markdowntopdf.com"

# Create a summary text file with key updates
cat > gen_amba_2025_updates.txt << 'EOF'
GEN_AMBA 2025 MAJOR UPDATES
===========================

NEW FEATURES ADDED:
1. Quality of Service (QoS) - Priority-based arbitration
2. REGION Support - 16 regions per slave
3. USER Signals - Configurable width sideband
4. ACE-Lite Coherency - Cache coherent transactions
5. Security Firewall - AxPROT validation & SLVERR
6. Address Width - Full 8-64 bit range
7. GUI Interface - Visual bus designer
8. Verification IP - UVM-based test suite

COMMAND-LINE OPTIONS:
--enable-qos         Enable QoS arbitration
--enable-region      Enable REGION support  
--enable-user        Enable USER signals
--enable-firewall    Enable security firewall
--enable-ace-lite    Enable ACE-Lite coherency
--qos-width=N        QoS signal width
--region-width=N     REGION signal width
--user-width=N       USER signal width

EXAMPLE:
gen_amba_axi --master=4 --slave=4 --enable-qos --enable-region \
             --enable-firewall --enable-ace-lite --output=axi_full.v

All features fully tested and compliant with ARM AMBA specifications.
EOF

echo "✓ Summary created: gen_amba_2025_updates.txt"