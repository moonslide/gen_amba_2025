Requirements for AMBA Tool GUI and Functionality Enhancements
Document ID: REQ-20250726-01
Date: July 26, 2025
Author: (User's Name/Team)

Objective
This document outlines the required enhancements for the AMBA Tool. The primary goals are to improve user interface (UI) usability, streamline the workflow for file/directory selection, and enhance the reliability and automation capabilities of the Verification IP (VIP) generation process.

1.0 GUI Usability Enhancements
1.1 Default Dialog Size for VIP Setup
Requirement: The show_vip_setup_dialog window shall, by default, be initialized to a size that is large enough to display all of its content, including the "Next Step" button.

Justification: The current default size is too small, forcing the user to manually resize the window or scroll to access critical navigation buttons. This change will improve workflow efficiency and user experience by making all essential controls immediately visible.

2.0 File/Directory Selection Workflow
2.1 Modal Dialog for Directory Selection
Requirement: When a user needs to select a destination folder, the tool must present a modal pop-up window that is a native system file/directory browser. The main application window should be inactive until the user completes the selection or cancels the dialog.

2.2 Status Indication and Confirmation
Requirement: The workflow for selecting a directory and generating files must provide clear, in-place feedback to the user within the same dialog/pane. The sequence shall be as follows:

After Selection: Once a folder is selected via the pop-up, the path of the selected folder shall be displayed in the GUI. A status message such as "Path selected. Ready for execution." should appear.

After Execution: Upon successful completion of the file generation or other process, the status message in the same dialog must be updated to confirm completion. This message must include the final, full path where the files were saved (e.g., "Success: VIP generated and saved to C:\projects\my_amba_vip").

Justification: This provides a clear and contained workflow. The user receives immediate confirmation of their selection and a final status report in the same context, preventing confusion about where the output files are located.

3.0 Verification IP (VIP) Enhancements
3.1 Replacement of Default AXI VIP
Requirement: The current standalone AXI VIP has been found to be non-functional. It shall be replaced. The tool must integrate and use the tim_axi4_vip available from the public Git repository as the new default for AXI VIP generation.

Source Repository: https://github.com/moonslide/tim_axi4_vip

Justification: The existing VIP is unusable. Using a proven, open-source VIP will provide a reliable and functional AXI VIP out-of-the-box, significantly improving the tool's value.

3.2 Automation for RTL Wrapper VIP Generation
Requirement: The functionality for the RTL_WRAPPER VIP option shall be significantly enhanced. In addition to generating the VIP components, the tool must also automatically perform the following steps:

RTL Wrapper Generation: Automatically generate the top-level RTL wrapper file (Verilog or VHDL) required to instantiate the VIP.

Automated Instantiation and Port Connection: Automatically connect the ports of the generated wrapper/VIP to the corresponding ports of the user's DUT (Device Under Test) within the generated testbench or environment.

Justification: This is a major automation feature that will save users significant time and reduce the potential for manual connection errors. It directly integrates the DUT with the verification environment, making the tool much more powerful and easier to use.
