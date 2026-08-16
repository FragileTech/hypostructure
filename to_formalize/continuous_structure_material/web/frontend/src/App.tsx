import { lazy, Suspense } from "react";
import { Navigate, Route, Routes } from "react-router-dom";

import { AppShell } from "./components/AppShell";

const DataPage = lazy(() => import("./pages/DataPage"));
const ErdosProofPage = lazy(() => import("./pages/ErdosProofPage"));
const SearchPage = lazy(() => import("./pages/SearchPage"));
const SourcePage = lazy(() => import("./pages/SourcePage"));
const NotFoundPage = lazy(() => import("./pages/NotFoundPage"));

function RouteFallback() {
  return (
    <section className="request-state" role="status">
      <span className="loading-mark" aria-hidden="true" />
      <p>Opening documentation…</p>
    </section>
  );
}

export default function App() {
  return (
    <AppShell>
      <Suspense fallback={<RouteFallback />}>
        <Routes>
          <Route path="/" element={<DataPage source={{ kind: "page", id: "home" }} />} />
          <Route path="/docs/getting-started" element={<DataPage source={{ kind: "page", id: "getting-started" }} />} />
          <Route path="/docs/problems" element={<DataPage source={{ kind: "page", id: "problems" }} />} />
          <Route path="/docs/dags" element={<DataPage source={{ kind: "page", id: "dags" }} />} />
          <Route path="/strategies" element={<DataPage source={{ kind: "page", id: "strategies" }} />} />
          <Route path="/strategies/:strategyId" element={<DataPage source={{ kind: "strategy", parameter: "strategyId" }} />} />
          <Route path="/examples" element={<DataPage source={{ kind: "page", id: "examples" }} />} />
          <Route path="/examples/erdos" element={<ErdosProofPage />} />
          <Route path="/examples/:exampleId" element={<DataPage source={{ kind: "example", parameter: "exampleId" }} />} />
          <Route path="/reference" element={<DataPage source={{ kind: "page", id: "reference" }} />} />
          <Route path="/reference/modules/:moduleId" element={<DataPage source={{ kind: "module", parameter: "moduleId" }} />} />
          <Route path="/reference/declarations/:declarationId" element={<DataPage source={{ kind: "declaration", parameter: "declarationId" }} />} />
          <Route path="/source/:sourceId" element={<SourcePage />} />
          <Route path="/search" element={<SearchPage />} />
          <Route path="/start" element={<Navigate replace to="/docs/getting-started" />} />
          <Route path="/core" element={<Navigate replace to="/docs/problems" />} />
          <Route path="/core/cts/*" element={<Navigate replace to="/strategies" />} />
          <Route path="/core/routes/*" element={<Navigate replace to="/docs/dags" />} />
          <Route path="/graph" element={<Navigate replace to="/examples/graph" />} />
          <Route path="/pde" element={<Navigate replace to="/examples/pde" />} />
          <Route path="*" element={<NotFoundPage />} />
        </Routes>
      </Suspense>
    </AppShell>
  );
}
