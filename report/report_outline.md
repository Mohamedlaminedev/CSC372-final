# CSC 372 Final Project Report Outline

## Team
- Mohamed Diakhate
- Andrew (add other teammates as needed)

## Submission checklist
- [ ] One-paragraph discussion per part (P1–P4)
- [ ] Model + temperature used for each run
- [ ] Prompt/response transcript with timestamps (satisfying + falsifying)
- [ ] Final C code (copy/pasted, not screenshots)
- [ ] `frama-c -wp <file>.c -then -report` output for each snippet
- [ ] Consolidated conclusion + lessons learned

## Structure
1. **Introduction** – goals, tooling, how LLM was used
2. **Methodology** – prompt template, verification flow, environment
3. **Per-part sections (P1–P4)**
   - Specification recap
   - Discussion paragraph
   - LLM settings (model, temperature)
   - Transcript tables (good + bad)
   - Final code blocks (good + bad)
   - Frama-C report snippets (good + bad)
4. **Validation summary** – what passed, what failed, interpretation of WP output
5. **Future work / lessons learned**

## Frama-C command template
```
frama-c -wp src/<file>.c -then -report > frama_reports/<file>_report.txt
```
Include the resulting text files alongside the report.
