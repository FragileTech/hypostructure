import { Navigate, Route, Routes } from "react-router-dom";

import { AppShell } from "./components/AppShell";
import { DocsHomePage } from "./docs/DocsHomePage";
import { DocsLayout } from "./docs/DocsLayout";
import { DocsPage } from "./docs/DocsPage";
import { ExplorePage } from "./pages/ExplorePage";
import { LandingPage } from "./pages/LandingPage";
import { NotFoundPage } from "./pages/NotFoundPage";
import { NotationPage } from "./pages/NotationPage";
import { OverviewPage } from "./pages/OverviewPage";
import { TablesPage } from "./pages/TablesPage";

export function App() {
  return (
    <Routes>
      <Route element={<AppShell />}>
        <Route index element={<LandingPage />} />
        <Route path="lean" element={<DocsLayout />}>
          <Route index element={<DocsHomePage />} />
          <Route path=":page" element={<DocsPage />} />
        </Route>
        <Route path=":proof" element={<OverviewPage />} />
        <Route path=":proof/explore" element={<ExplorePage />} />
        <Route path=":proof/tables" element={<TablesPage />} />
        <Route path=":proof/notation" element={<NotationPage />} />
        {/* The site used to serve one proof from the root. */}
        <Route path="explore" element={<Navigate to="/erdos-gyarfas/explore" replace />} />
        <Route path="notation" element={<Navigate to="/erdos-gyarfas/notation" replace />} />
        <Route path="*" element={<NotFoundPage />} />
      </Route>
    </Routes>
  );
}
