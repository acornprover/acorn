// Interfaces with the language server.
// This should be kept parallel to interfaces.rs.

interface DocumentProgress {
  version: number;
  verified: [number, number][];
}

interface ProgressResponse {
  buildId: number | null;
  done: number;
  total: number;
  finished: boolean;
  docs: { [url: string]: DocumentProgress };
}

interface Position {
  line: number;
  character: number;
}

interface Range {
  start: Position;
  end: Position;
}

interface Location {
  uri: string;
  range: Range;
}

interface SelectionParams {
  uri: string;
  version: number;
  selectedLine: number;
  id: number;
}

interface Step {
  statement: string;
  reason: string;
  location: Location | null;
}

interface GoalInfo {
  goalName: string;
  hasCachedProof: boolean;
  steps: Array<Step> | null;
}

interface CitationInfo {
  selectionText: string;
  range: Range;
  theoremName: string | null;
  theoremLocation: Location | null;
  expansion: string;
}

interface SelectionResponse {
  uri: string;
  version: number;
  failure: string | null;
  loading: boolean;
  building: boolean;
  goalRange: Range | null;
  goals: Array<GoalInfo>;
  citation: CitationInfo | null;
  id: number;
}

// This section is for the extension to communicate with the assistant.
// There's no Rust equivalent for these interfaces.

// Sent from the extension to the assistant to indicate that the user might need help.
// Any selection response will override these.
interface Help {
  // The user has just created a new document, so they might need to know how to get started.
  newDocument?: boolean;

  // There's stuff in the document, but we don't have anything selected.
  noSelection?: boolean;
}
