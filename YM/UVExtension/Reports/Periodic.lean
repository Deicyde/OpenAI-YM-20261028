import YM.UVExtension.Reports.Prefixes
/-!
 Proof spelling out periodicity on the NoHit universal-cover
 formulation, in case of placements straddling representative seams.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Beach
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open Source Labels Gale Mast MergeProof Cells GridApprox Accent Extra.Histories
open Swell Stock Harvest Extraction Fallow Poppy
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section cover
variable (S : Schedule) (N p n : ℕ)

def changeReps (x:Tabletop n)(v : Points n):= v+Extraction.tag (Extraction.length S p) x
abbrev integerShift (x:Tabletop n) : Tabletop n := (S.side N p).val • x

lemma ceilShift (x:Tabletop n) (v:Points n): Extraction.address (S.a N) (changeReps S p n x v) =
    Extraction.address (S.a N) v + integerShift S N p n x := by
  ext i j
  change ⌈(v i j + Extraction.length S p * (x i j : ℝ)) / S.a N⌉ =
    ⌈v i j / S.a N⌉ + ( ((S.side N p).val) • x i j)
  rw [show (v i j+ _*_) / _= v i j / S.a N+ (( ( (S.side N p).val) • x i j : ℤ):ℝ) from ?_,Int.ceil_add_intCast]
  unfold Extraction.length
  rw [← S.span_side N p,add_div]
  simp only [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]; field_simp [((S.a_pos N).ne')]

lemma wrap_shift_invisible (x:Tabletop n) (v:Tabletop n):
    wrap (S.side N p) ∘ (x+integerShift S N p n v) = wrap _ ∘ x :=by
  funext i; simp only [comp_apply,Pi.add_apply,map_add,add_eq_left]
  funext j
  change ( (( ((S.side N p).val) • (v i j) : ℤ) : Per (S.side N p))) = 0
  simp [Per]

lemma away_images (x:Tabletop n)(v:Points n)(h:v ∈ NoHit S p n) : changeReps S p n x v∈ NoHit S p n :=by
  intro i j hij; obtain ⟨k,hk⟩:= h i j hij
  refine ⟨k,?_⟩; rintro ⟨r,hr⟩
  change (v i k+Extraction.length S p*(x i k:ℝ)) - (v j k+Extraction.length S p*(x j k:ℝ))= _ at hr
  apply hk; refine ⟨r+ x j k-x i k,?_⟩; push_cast; linarith only [hr]

lemma climbs_same (F : Tabletop n→ℂ) (v : Tabletop n)(h : ∀ x,F (x+v)=F x) (l:List (Axel n))(x:Tabletop n) :
    Fallow.rake (S.a N) F l (x+v)= Fallow.rake (S.a N) F l x:=by
  induction l generalizing x with
  | nil=> exact h _
  | cons a l ih=> unfold Fallow.rake Fallow.climbing; rw [add_right_comm x v _,ih (x+hike a),ih]
end cover

variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D}
    {Q:Factor A} {S:Uses Q hG} {C:ℕ→ℝ}{w:Bid.Worth}{R:Bandage Q C w} {t:ℕ→ℕ}{L:Cellar S t R}
    {p n:ℕ} {a :ℝ} (ha:0<a){hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a}
    {u : Fin n→ (roster L).Token} {W: ℕ→ℂ→ Tabletop n→ℂ}{f:ℂ→ Points n→ℂ}{m:ℕ}
    (H: Shoal L p n u a hp W f m)
open Cellar
include ha H
lemma periodic_caps (x:Tabletop n) (l:List (Axel n)) (hl:l.length ≤ m)
    (v:Points n) (hx:v∈NoHit A.B.a.S p n) (z:ℂ) (hz:z∈Metric.ball 0 a) :
    ivy (f z) l (changeReps A.B.a.S p n x v) = ivy (f z) l v:=by
  let T:= A.B.a.S; let b:= changeReps T p n x v
  have hb : b∈NoHit T p n := away_images _ _ _ x v hx
  have hv : (fun i=> rails T W l i z b) =ᶠ[atTop] (fun i=> rails T W l i z v) :=by
    filter_upwards [H.top] with i hi
    have h (x' : Tabletop n) : W i z (x'+integerShift T i p n x)=W i z x' :=by
      let y := x' + integerShift T i p n x
      refine (desk a ha).agrees (fun z=> W i z y) (fun z=> W i z x')
        (bumps _ _ ((hi.1 _).differentiableOn)) (bumps _ _ ((hi.1 _).differentiableOn))
        (fun d=> ?_) hz
      let k : Orchard.Keys S := fun _ _=> roseK S ha hp d
      change W i ((k i p).val:ℂ) y= W i ((k i p).val:ℂ) x'
      rw [hi.2 k ((desk _ ha).within d)]
      exact congr_arg ((yard k L).numeric i p u) (wrap_shift_invisible T i p n x' x)
    unfold rails Ink
    rw [ceilShift (S:=T)] -- b reducible?
    exact climbs_same _ i n _ _ h _ _
  have h (x':Points n)(hY:x'∈ NoHit T p n) : Tendsto (fun i=> rails T W l i z x') atTop (𝓝 (ivy (f z) l x')) := by
    refine Metric.tendsto_nhds.mpr fun ε he=> ?_
    filter_upwards [(H.roles.loop l hl).converges {z} isCompact_singleton (Set.singleton_subset_iff.mpr hz) {x'} isCompact_singleton (singleton_subset_iff.mpr hY) 0 ε he] with i hi
    rw [dist_eq_norm]
    simpa only [iteratedDeriv_zero] using! hi z (mem_singleton z) x' (mem_singleton _)
  exact tendsto_nhds_unique ((h _ hb).congr' hv) (h _ hx)
end YM.UVExtension.Beach
