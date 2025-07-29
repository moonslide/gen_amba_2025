#!/bin/bash
# Generate complete user guide PDF

echo "Generating AMBA Bus Matrix complete user guide..."

# Get the directory where this script is located
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
GUI_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
USER_GUIDE_DIR="$GUI_DIR/docs/user_guide_generator"

# Change to user guide generator directory
cd "$USER_GUIDE_DIR"

if [ ! -f "create_complete_guide.py" ]; then
    echo "Error: PDF generator not found at $USER_GUIDE_DIR/create_complete_guide.py"
    exit 1
fi

python3 create_complete_guide.py

if [ $? -eq 0 ]; then
    echo "✅ User guide generated successfully!"
    echo "📄 File location: $GUI_DIR/docs/AMBA_Bus_Matrix_Complete_User_Guide.pdf"
else
    echo "❌ User guide generation failed"
    exit 1
fi