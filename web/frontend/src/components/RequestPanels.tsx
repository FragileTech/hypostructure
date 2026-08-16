export function LoadingPanel() {
  return (
    <div className="request-panel" role="status">
      <span className="spinner" aria-hidden="true" />
      <p>Reading the proof…</p>
    </div>
  );
}

export function ErrorPanel({ error }: { error: Error }) {
  return (
    <div className="request-panel is-error" role="alert">
      <h2>The proof diagram could not be loaded</h2>
      <p>{error.message}</p>
      <p className="request-panel-hint">
        Regenerate it with <code>python web/tools/extract_proof_graph.py</code>.
      </p>
    </div>
  );
}
