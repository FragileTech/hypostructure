/** Structural vocabulary shared with the external proof controller. */
import register from "../../../../tools/methodology_gate/policy/structural-register.json";

export type TechniqueId = "T01" | "T02" | "T03" | "T04" | "T05" | "T06" | "T07" | "T08" | "T09" | "T10" | "T11" | "T12" | "T13" | "T14" | "T15" | "T16" | "T17" | "T18" | "T19";
export type PropertyId = "A01" | "A02" | "A03" | "A04" | "A05" | "A06" | "A07" | "A08" | "A09" | "A10" | "A11" | "A12" | "A13" | "A14" | "B01" | "B02" | "B03" | "B04" | "B05" | "B06" | "B07" | "B08" | "B09" | "C01" | "C02" | "C03" | "C04" | "C05" | "C06" | "C07" | "C08" | "C09" | "C10" | "C11" | "C12" | "C13" | "D01" | "D02" | "D03" | "D04" | "D05" | "D06" | "D07" | "D08" | "D09" | "D10" | "E01" | "E02" | "E03" | "E04" | "E05" | "E06" | "E07" | "E08" | "E09" | "F01" | "F02" | "F03" | "F04" | "F05" | "F06" | "F07" | "F08" | "G01" | "G02" | "G03" | "G04" | "G05" | "G06" | "G07" | "G08" | "G09" | "H01" | "H02" | "H03" | "H04" | "H05" | "H06" | "H07" | "H08" | "H09" | "H10" | "I01" | "I02" | "I03" | "I04" | "I05" | "I06";

export interface StructuralProperty {
  id: PropertyId;
  name: string;
  observable: string;
  techniques: readonly TechniqueId[];
  certificate: string;
  caveat: string;
}
export interface StructuralPropertyGroup {
  id: string;
  title: string;
  properties: readonly StructuralProperty[];
}
export type SurveyStructuralProperty = StructuralProperty;
export const STRUCTURAL_TECHNIQUES = register.techniques as readonly {
  id: TechniqueId; name: string; move: string;
}[];
export const STRUCTURAL_PROPERTY_GROUPS = register.groups as readonly StructuralPropertyGroup[];

export interface EGInvariantBinding {
  number: number;
  propertyIds: readonly PropertyId[];
  techniqueIds: readonly TechniqueId[];
  primaryItem: string;
}

const eg = (
  number: number,
  propertyIds: readonly PropertyId[],
  techniqueIds: readonly TechniqueId[],
  primaryItem: string,
): EGInvariantBinding => ({ number, propertyIds, techniqueIds, primaryItem });

export const EG_INVARIANT_BINDINGS = [
  eg(1, ["C02", "C03", "C04"], ["T08", "T09"], "lem:return-equivalence"),
  eg(2, ["A07", "E01", "E02"], ["T02", "T03", "T04"], "lem:no-proper-core"),
  eg(3, ["E03"], ["T02", "T03"], "lem:deletion-critical"),
  eg(4, ["A06"], ["T02", "T03", "T07"], "lem:deletion-critical"),
  eg(5, ["A08", "E04"], ["T03", "T04"], "lem:stub-positive"),
  eg(6, ["B07", "E05", "E07"], ["T02", "T03", "T05", "T16"], "lem:replacement"),
  eg(7, ["B07", "E06"], ["T05", "T16"], "lem:context-universality"),
  eg(8, ["E05"], ["T02", "T03", "T05"], "cor:uncompressible"),
  eg(9, ["A01", "A02", "A03", "A04"], ["T01"], "lem:cycle-rank"),
  eg(10, ["A02", "A13"], ["T01", "T02"], "lem:sparse-upper-envelope"),
  eg(11, ["A12"], ["T01", "T11"], "lem:cycle-rank"),
  eg(12, ["A12", "A13", "H09"], ["T01"], "lem:near-cubic-budget"),
  eg(13, ["A05", "A12", "H01"], ["T01", "T13"], "lem:netcharge-superadd"),
  eg(14, ["A05", "A06", "A14", "H08"], ["T01", "T12", "T13", "T14", "T15"], "prop:nonnear-cubic-sharp-overload-routing"),
  eg(15, ["A02", "A14", "G01"], ["T01", "T12"], "lem:near-cubic-budget"),
  eg(16, ["A08", "D03", "I05"], ["T07", "T13", "T17"], "lem:fan-certificate"),
  eg(17, ["C01", "C04", "D02"], ["T07", "T09", "T17"], "lem:fan-certificate"),
  eg(18, ["C01", "D07"], ["T09", "T16", "T17"], "lem:fan-certificate"),
  eg(19, ["A05", "C01"], ["T01", "T07", "T13", "T17"], "lem:fan-certificate"),
  eg(20, ["C08", "C09", "G09"], ["T06", "T12"], "prop:p13-density"),
  eg(21, ["C09", "C10"], ["T06", "T12"], "lem:stub-positive"),
  eg(22, ["C08", "C10"], ["T06"], "lem:remainder-empty-internal-3-core"),
  eg(23, ["A10", "B09"], ["T01", "T14", "T15"], "lem:stub-positive"),
  eg(24, ["A11", "H01"], ["T01", "T13"], "lem:stub-positive"),
  eg(25, ["D01", "D02", "I01", "I02"], ["T07", "T17"], "lem:labels"),
  eg(26, ["A09", "F01"], ["T01", "T07", "T17"], "lem:curv-enum"),
  eg(27, ["G02", "G03"], ["T11", "T12"], "cor:forced-curvature-cost"),
  eg(28, ["A09", "F01"], ["T01", "T07", "T15"], "lem:wedge-lower"),
  eg(29, ["F02", "F07", "H09"], ["T11", "T12"], "lem:full-rank"),
  eg(30, ["C05"], ["T08"], "lem:two-path-criterion"),
  eg(31, ["C05"], ["T08", "T09"], "lem:replacement"),
  eg(32, ["C06"], ["T04", "T08"], "lem:context-universality"),
  eg(33, ["C07"], ["T08", "T11"], "lem:context-universality"),
  eg(34, ["F03", "F04"], ["T10", "T11"], "lem:proper-smearing"),
  eg(35, ["F06"], ["T08", "T10", "T11"], "lem:smearing-support-repair"),
  eg(36, ["C04", "F01"], ["T08", "T09"], "lem:return-equivalence"),
  eg(37, ["F05"], ["T05", "T10", "T11"], "lem:separated-testers"),
  eg(38, ["F05", "F07"], ["T05", "T11"], "lem:separated-testers"),
] as const satisfies readonly EGInvariantBinding[];

export const ALL_STRUCTURAL_PROPERTIES: readonly SurveyStructuralProperty[] =
  STRUCTURAL_PROPERTY_GROUPS.flatMap(
    (group): readonly SurveyStructuralProperty[] => group.properties,
  );

export const STRUCTURAL_SURVEY_PART_ANCHOR = "methodology-survey";

export function techniqueAnchor(id: TechniqueId): string {
  return `methodology-technique-${id}`;
}

export function propertyAnchor(id: PropertyId): string {
  return `methodology-property-${id}`;
}
