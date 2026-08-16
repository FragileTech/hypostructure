import { Navigate, Route, Routes } from "react-router-dom";

import { AppShell } from "./components/AppShell";
import { ExplorePage } from "./pages/ExplorePage";
import { LandingPage } from "./pages/LandingPage";
import { NotFoundPage } from "./pages/NotFoundPage";
import { NotationPage } from "./pages/NotationPage";
import { OverviewPage } from "./pages/OverviewPage";

export function App() {
  return (
    <Routes>
      <Route element={<AppShell />}>
        <Route index element={<LandingPage />} />
        <Route path=":proof" element={<OverviewPage />} />
        <Route path=":proof/explore" element={<ExplorePage />} />
        <Route path=":proof/notation" element={<NotationPage />} />
        {/* The site used to serve one proof from the root. */}
        <Route path="explore" element={<Navigate to="/erdos-gyarfas/explore" replace />} />
        <Route path="notation" element={<Navigate to="/erdos-gyarfas/notation" replace />} />
        <Route path="*" element={<NotFoundPage />} />
      </Route>
    </Routes>
  );
}
