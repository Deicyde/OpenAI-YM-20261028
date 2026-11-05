import YM.TraceExtension.Shelves.Tonic
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shelves
open Function Filter Lattice RG Wilson Labels Source Extra.Histories Bid MergeProof.Accent MergeProof
open Extraction Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Climb Analysis Work
open MeasureTheory
open Further.PhysicalPeriodLimitF933 Shunt Weir PhysicalNext.Repeat.Legato.Bandage Push.GridApprox Cells
open Relay Pull Terrace Terrace.Glade Slate Perfect Turret Margin
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
variable (P:C.Makes) (h:G.Simple) (θ:PostT C.path.levels)(K:Stock.Tabs C.path.levels)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (ht:Scrim C W u ψ φ δ (fly C.path.levels) r D)(hM:Sceptre C W) (hT:supportQ C.path.levels)
variable {F:Extraction.Order}{𝓛:Ultrafilter (ℕ×ℕ)} (hb:(𝓛:Filter (ℕ×ℕ))≤F.fuse)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "V!"=> C.path
local notation "b!"=> (𝓛:Filter (ℕ×ℕ))
local notation "H!"=> C.path.levels.clock.hatBeta
variable {t:Tickets C} (hu:Grant C (𝓛:Filter (ℕ×ℕ)) t)
open Zn
variable {d:ℕ}{Z:Arch C}(hz:steep 𝓛 Z)
open Finset StressFlux
open Next.UVStress Asymptotics
variable {S: Table C.book} (HE:S.Hierarchy)(hx:CellHyp C F)(hp:F.PointLimits C S) {Y:DiffPlan S}(hf:Y.Derivatives S)
section maps
variable {S₁:Schedule}{E F':Type*}[NormedAddCommGroup E][NormedAddCommGroup F'][NormedSpace ℝ E][NormedSpace ℝ F'] {f g:ℕ→E}
lemma fast_map(h: Fast S₁ f)(L:E→L[ℝ] F'): Fast S₁ fun i=>L (f i):=h.smaller (isBigO_iff.mpr ⟨‖L‖,Eventually.of_forall fun i=> L.le_opNorm (f i) ⟩)
lemma fast_bill [FiniteDimensional ℝ E] (h:Fast S₁ f)(v:E→ₗ[ℝ] F'): Fast S₁ fun i=>v (f i):= fast_map h v.toContinuousLinearMap
lemma fast_scale(h:Fast S₁ f)(v:ℝ): Fast S₁ fun i=>v • f i:=fast_map h (F':=E) (v • ContinuousLinearMap.id ℝ E)
end maps
-- now rank representations.
variable (ho:Y.Orientation HE.spin) (he:Grant C (𝓛:Filter (ℕ×ℕ)) t)
def Pole(L:PaceBook C)(k:ℕ):=Reed (Prism (C.labels.level 5)) fun i=> (L.Z i).x k
include hf
lemma bar_nab (L:PaceBook C)(k:ℕ): nabla Y (baron S L k)=nabla Y (Plot (Ard HE 4) (inter (Storm S L k))):=by
    funext i; unfold nabla baron; refine Finset.sum_congr rfl fun b _=>?_; rw[value_center,map_sub,map_smul, Y.unit_drop HE.laws hf HE.smooth]; simp only [smul_zero,sub_zero]; refine congr_arg _ ?_; unfold press; rw [portrait_4]; exact congr_fun (congr_fun (congr_arg (Plot (Ard HE 4)) (funext fun i=> funext fun j=> inter_link (S:=S) (StormP C L k) i j)) b) i
include P h ht hM hT K hb θ hx hp he ho HE
lemma curtain' (i:Bend)(L:PaceBook C)(hL:Rod t i b! L)(a:Axis): Fast C.S fun k=> nabla Y (baron S L k) a - S.project 5 (Pole L k a):=by
    let f(k):= Storm S L k; let g(k):= inter (f k)
    have ht₁(i' j:Axis) : Fast C.S (fun k=> Y.deriv 4 i' (g k i' j)-Portrait S (L.Zp i' j) k):=by
       let y(k):= f k j i' - f k i' j; have hZ: Fast C.S y:= merit P h θ K ht hM hT hb he HE hx hp hL j i'
       let E:= (Y.deriv 4 i').restrictScalars ℝ; have hG: Fast C.S (fun k=> E ((1/2:ℝ) • y k)):= fast_bill (fast_scale hZ (1/2)) E
       have hu: Fast C.S (fun k=> E (f k i' j)-Portrait S (L.Zp i' j) k):=scores P h K hb he HE hx hp hf i i' j L hL
       have hx(k:ℕ): g k i' j=f k i' j+(1/2:ℝ) • y k:=by unfold g y inter; module
       have hz : (fun k=>Y.deriv 4 i' (g k i' j)-Portrait S (L.Zp i' j) k)=(fun k=>E ((1/2:ℝ) • y k))+(fun k=>E (f k i' j)-Portrait S (L.Zp i' j) k):=by ext1 k; rw [hx]; change E (_+_)-_=_+_;rw [map_add];abel_nf; rw [add_left_comm]
       rw[hz]; exact hG.add hu
    let z(a k):=Portrait S (L.Z a) k
    let u(a k):= nabla Y (g k) a-z a k
    have hf'(b): Fast C.S (u b):=by
        let D'(a k):= Y.deriv 4 a (g k a b)-Portrait S (L.Zp a b) k
        have hz : u b=(fun k=>∑ a:Axis,D' a k)+(fun k=>(∑ a:Axis, Portrait S (L.Zp a b) k)-z b k):=by funext k; unfold u nabla D'; simp [Finset.sum_sub_distrib]
        rw[hz]; exact (fast_fin D' Finset.univ (fun a _=> ht₁ a b)).add (sky P h K hb he HE hx hp i L hL b)
    have hp(k:ℕ): nabla Y (baron S L k) a - S.project 5 (Pole L k a)=∑ m:Motion,(Glade.rent*hued m a) • Ard HE 5 m (u (prev m a) k):=by
       rw [bar_nab HE hf,primary_nab HE ho]; unfold Pole; rw [portrait_5 HE, reedEq, reedEq, ← Finset.sum_sub_distrib]; simp_rw [← smul_sub,← map_sub]; rfl
    simp_rw [hp]; exact fast_fin _ Finset.univ (fun i _=>fast_scale (fast_bill (hf' _) (Ard HE 5 i)) _)
omit ho hf
lemma Thin(i:Bend)(L:PaceBook C)(hL:Rod t i b! L)(h':i≠some true): Fast C.S (fun k=>∑ a:Axis,baron S L k a a):=by
    have hp₁:Fast C.S (fun k=> ∑ i:Axis, Storm S L k i i):=by
        rcases i with _|a; exact trace_sf P h θ K ht hM hT hb he HE hx hp hL; cases a; exact trace_bs P h θ K ht hM hT hb he HE hx hp hL; exact False.elim (h' rfl)
    let y(k):= ∑ i:Axis, Storm S L k i i; let G' (t):= Ard HE 4 t; let U(k):= inter (Storm S L k); let T₁:=(centering S 4).restrictScalars ℝ
    have hz(k i j): (S.project 4) (press L k i j)=Plot G' (U k) i j:=by
        unfold press; rw [portrait_4 HE]; exact congr_fun (congr_fun (congr_arg (Plot (Ard HE 4)) (funext fun a=> funext fun b=> inter_link (S:=S) (StormP C L k) a b)) i) j
    have hx(k i j): baron S L k i j=T₁ (Plot G' (U k) i j):= by unfold baron; rw [hz]; rfl
    have hy(m:Motion)(i:Axis): Glade.rent *hued m i * hued m i=Glade.rent:=by unfold hued StressFlux.sign;split<;>ring
    have hU(k:ℕ):(∑ i:Axis,baron S L k i i)=∑ m:Motion, T₁ (Glade.rent • G' m (y k)):=by
       simp_rw [hx]; rw [← map_sum]; refine Eq.trans (b:=T₁ (∑ m:Motion,Glade.rent • G' m (y k))) ?_ (map_sum ..); apply congr_arg; rw [Finset.sum_congr rfl (g:=fun i:Axis=>∑ m:Motion,Glade.rent • G' m (U k (prev m i) (prev m i))) (fun i _=>by rw [plotEq]; exact sum_congr rfl (fun m _=>by rw[hy]))]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun m _=>?_ ; rw [← Finset.smul_sum, ←map_sum (G' m)]; unfold U; simp_rw [inter_unit]; unfold prev; rw [Equiv.sum_comp m.1.perm.symm (fun j=> Storm S L k j j)]
    simp_rw[hU];exact fast_fin (fun m:Motion=>fun k=>T₁ (Glade.rent • G' m (y k))) univ fun i _=> fast_bill (fast_scale (fast_bill hp₁ (G' i)) _) _
end YM.Trace.Shelves
