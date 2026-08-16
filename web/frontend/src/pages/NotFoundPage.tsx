import { Link } from "react-router-dom";

export function NotFoundPage() {
  return (
    <div className="request-panel">
      <h2>There is no page here</h2>
      <p>
        Pick a proof from <Link to="/">the front page</Link>.
      </p>
    </div>
  );
}
