# CSC 372 Final Project

This repository tracks the Frama-C final project deliverables (P1–P4) for Mohamed Diakhate, Andrew, and teammates. Structure:

- `src/`: ACSL-annotated C snippets (good + bad implementations for each spec)
- `frama_reports/`: output from `frama-c -wp <file>.c -then -report`
- `transcripts/`: raw LLM prompt/response logs with timestamps and model settings
- `report/`: final write-up (PDF) plus any drafts/notes
- `Final_Project_CSC372 (2).pdf`: assignment prompt for reference

Next actions:
1. Create ACSL/C templates for P1–P4 inside `src/`.
2. Run LLM prompts for each template (two versions per spec) and capture transcripts.
3. Execute Frama-C on each snippet and save the reports.
4. Compile discussion, transcripts, code, and reports into the final PDF in `report/`.
