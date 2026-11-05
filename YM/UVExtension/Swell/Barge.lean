import YM.UVExtension.Swell.Moor
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Swell
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet MeasureTheory Push Push.AbsoluteSums
open RG.Supply Precision Shoot Org Input Steady
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext Mallow
open WilsonStartup Time Next.Foundations UVNext.CouplingReset Legato
open Roost Spire Orchard Camp Dales Lamppost Oriel Rafter Copse Linden Metric
open SectorNext.Vacuum Hearth Pier MergeProof.Ribbons
open Source Labels Gale Mast MergeProof Cells GridApprox Accent Extra.Histories
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {Q:Factor A} {S: Uses Q hG} {C:ℕ→ℝ}{w:Bid.Worth}{R: Bandage Q C w} {t:ℕ→ℕ}(L:Cellar S t R)
    (N n m k d:ℕ) {a z:ℝ}(ha:0<a)(hp:Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a)
local notation "T"=> A.B.a.S
local notation "P"=> A.B.a.budget m
local notation "R0"=> desk a ha
local notation "ℍ"=> Row a
local notation "V"=> (A.B.a.budget m)
set_option quotPrecheck false
local notation "F"=> (frames G).level d
local notation "J"=> (F).Index
variable (V₁:Levels G)
private def pay (i:J):= (V₁.S.a m)⁻¹^d*(WilsonStartup.Mark.scale (localSection G d) (V₁.budget m)*(F).coeffSize (Size.axis (F) i))
private def token (i:J):=(V₁.S.a m)⁻¹^d*(‖Size.axis (F) i 0‖+WilsonStartup.Mark.scale (localSection G d) (V₁.budget m)*(F).coeffSize ((F).core (Size.axis (F) i)))
def costP (m d:ℕ)(i:((frames G).level d).Index):= pay m d V₁ i + token m d V₁ i
private lemma prop (x:(F).Coeff)(U:Config G (V₁.S.side m n)): ‖beamP V₁ m n d x U‖≤ (V₁.S.a m)⁻¹^d * (WilsonStartup.Mark.scale (localSection G d) (V₁.budget m)*(F).coeffSize x):=by
    unfold beamP; simp only [Pi.smul_apply,norm_smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg (V₁.S.a_pos _).le, ←inv_pow]; exact mul_le_mul_of_nonneg_left (WilsonStartup.Mark.whole_scaled ..) (pow_nonneg (inv_nonneg.mpr (V₁.S.a_pos _).le) _)
lemma pricing (i:J)(U:Config G (V₁.S.side m n)): ‖beamP V₁ m n d (Size.axis (F) i) U‖ ≤ costP V₁ m d i ∧ ‖lampP V₁ m n d (Size.axis (F) i) U‖ ≤ costP V₁ m d i:=by
    let q:= WilsonStartup.Mark.scale (localSection G d) (V₁.budget m); have hq:0≤q:= (WilsonStartup.Mark.scale_pos _ _).le; let f:= Size.axis (F) i; have ht: 0 ≤ q * (F).coeffSize ((F).core f):= mul_nonneg hq (WilsonStartup.Mark.coeff_nn _); let k:= (V₁.S.a m)⁻¹^d; have hk : 0 ≤k := pow_nonneg (inv_nonneg.mpr (V₁.S.a_pos _).le) _
    have hp:= prop n m d V₁ f U; have h: ‖lampP V₁ m n d f U‖≤token m d V₁ i:=by
       unfold lampP; apply (norm_add_le ..).trans; unfold token; rw [mul_add,norm_mul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg (V₁.S.a_pos _).le,← inv_pow]; apply add_le_add le_rfl
       by_cases h:Healthy (V₁.budget m).threshold ((localSection G d).footprint 0) U
       · rw [masked_eq _ _ _ _ h]; exact prop ..
       rw [masked_ne _ _ _ _ h,norm_zero]; exact mul_nonneg hk ht
    exact ⟨hp.trans (le_add_of_nonneg_right ((norm_nonneg _).trans h)), h.trans (le_add_of_nonneg_left ((norm_nonneg _).trans hp))⟩
lemma holds (i:J): PolyB V₁.S (fun j=>costP V₁ j d i):=by
    let P' j:= WilsonStartup.Mark.scale (localSection G d) (V₁.budget j); have he :PolyB V₁.S P':= ((theta V₁).pow _).mul (PolyB.const ..); have hp:= (PolyB.inverse V₁.S).pow d
    exact (hp.mul (he.mul (PolyB.const ..))).add (hp.mul ((PolyB.const ..).add (he.mul (PolyB.const ..))))
variable {o:Side}(O:Fin k→ Site o)(l: Fin k→ℕ)
def bagW (S:Site o)(r:ℕ):= (Lattice.box r).image (fun j=>Lattice.wrap o j + S)
lemma ports (t:Site o)(v:ℕ): ((bagW t v): Set (Site o))= GridApprox.window t v:=by ext x; exact ⟨fun h=> Finset.mem_image.mp h,fun ⟨x,hx,h⟩=>Finset.mem_image.mpr ⟨x,hx,h⟩⟩
def garment : Support o:= {0}∪ Finset.univ.biUnion (fun i=>bagW (O i) (l i))
-- union multicov even when origins tied.
private lemma tiles (b i:ℕ)(hp:0<b)(x:Site o): coverNumber b (bagW x i) ≤ (i+i+1)^4 :=by
    refine (Corona.cover_mono ?_ b).trans (Corona.tile x i b hp); intro y hy; obtain ⟨z,hz,rfl⟩:= Finset.mem_image.mp hy; exact halo_spec.mpr ⟨x,Finset.mem_singleton_self _, (Work.E08.separation_box_add _ hz).trans (Nat.le_mul_of_pos_right i hp)⟩
lemma lengths (t:ℕ)(h:0<t): (0:Site o)∈ garment k O l ∧ Copse.cover k t (garment k O l)≤1+∑ i, ((l i)+(l i)+1)^4∧ (garment k O l).card ≤1+∑ i, (box (l i)).card:=by
    refine ⟨Finset.mem_union_left _ (Finset.mem_singleton_self _),?_,(Finset.card_union_le ..).trans (add_le_add (by simp) ((Finset.card_biUnion_le ..).trans (Finset.sum_le_sum fun i _=> Finset.card_image_le)))⟩
    let P':= Fin.cons (α:=fun _:Fin (k+1)=>Support o) (bagW (0:Site o) 0) (fun i=>bagW (O i) (l i))
    have he : (0:Site o)∈ P' 0 := by change 0 ∈ (↑(bagW (0:Site o) 0): Set (Site o)); exact (ports _ _).symm ▸ GridApprox.window_home 0 0
    apply (Copse.cheaper k t (garment k O l) P' (fun i hi=>?_)).trans; swap
    · rcases Finset.mem_union.mp hi with hi|hi; · exact Finset.mem_biUnion.mpr ⟨0,Finset.mem_univ _, (Finset.mem_singleton.mp hi) ▸ he⟩
      obtain ⟨i,h,hx⟩:= Finset.mem_biUnion.mp hi; exact Finset.mem_biUnion.mpr ⟨i.succ,Finset.mem_univ _, hx⟩
    rw [Fin.sum_univ_succ]; exact add_le_add (by simpa using! tiles t 0 h (0:Site o)) (Finset.sum_le_sum fun j _=> tiles t _ h _)

variable (W:Fin k→ Config G o→ℂ)
def cargo (k:ℕ){o:Side}(O:Fin k→Site o)(W:Fin k→ Config G o→ℂ)(U:Config G o): ℂ:= ∏ i,W i (translate (O i) U)
lemma loaded (h:∀ i, Interior (GridApprox.window 0 (l i)) (W i)): Interior (garment k O l) (cargo k O W):=by
   refine Interior.combines (fun i U=> W i (translate (O i) U)) (K:=((garment k O l):Set (Site o))) Finset.univ (fun i hi=>?_); have ht:= translated_window (O i) (h i); rw [zero_add,← ports] at ht; exact ht.enlarges fun j hj=> Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,hj⟩)
end YM.UVExtension.Swell
