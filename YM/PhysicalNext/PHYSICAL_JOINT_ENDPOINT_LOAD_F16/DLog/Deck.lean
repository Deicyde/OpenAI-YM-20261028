import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Creed
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Confirmed
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.SectorLie
import YM.B70NonflatLogdetConnection
import YM.Next.MAXWELL.Silt
import YM.Push.COMMON_WITNESSES.Fields
import YM.UVNext.PRICED_KERNELS.Echo


/-!
# Fsct on the same term/law: deck for determinant exponent letters

Companion supplier to Install. These are FULL physical determinant terms,
not the log of a marginal inverse in FKer's density. Use literal endpoint
window SectorChange. Need k even for `Wake` uses when paying a simultaneously
selected set; flag geometry kept at base V. Even if testing letters in a
fixed-chart germ about V, this has NO meaning as recomputing geometry or
changing sectors to extend across masks.

No new Gaussian formulas. Already proved `Covariance.coverall` purchase &
B70NonflatLogdetConnection (and at origin in another notation similar
B70NonflatOrderedConnection). Unify the paid `atom` coordinates AT the
uniform smaller log neighbourhood with the positions/frames from
SelectedOrderedKernels. That allows buying all the derivative slots of
RelativeLogdet.Physical.* with *their* `faceBudget` as tested rate.
Receipt for ∑ incl ordered Lie derivatives and `Install` application in
following files. In particular don't duplicate the Taylor log formulas.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.EndpointLoadF16.DetLong
open Function Filter Lattice RG Wilson Pressure Tree Matrix
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Completion
open FreeResolvent FreeResolvent.TestD FreeResolvent.Affine
open SelectedOrderedKernels AnalyticBridge AnalyticBridge.RelativeLogdet Physical Differential
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f}
    {P : Patch} {p : Teller G} {V : Config G c} {A : Stores S}
    {F : Forest S.ratio} {s : S.Choices} {T : Tube G S} {B : Directions G c}
    {k u l : ℕ} {x C D r σ b a v η w i γ δ : ℝ}

section unified

def tag (t : raw G c) : Covariance.Atom G c := (edge t,t.2.2)
lemma tag_map (t : raw G c) : Covariance.atom (tag t) = unitDir t := by
  rw [show Covariance.atom (tag t)=_ from Next.SectorChange.on_axis _]
  funext e; by_cases h : e=edge t
  · change (Pi.single (edge t) _ _) = _
    rw [h,unit_here,Pi.single_eq_same]; simp only [EuclideanSpace.basisFun_apply]; rfl
  change (Pi.single (edge t) _ _) = _
  rw [Pi.single_eq_of_ne h,unit_off _ _ h]

abbrev marked (G : Gauge) (c : Side) (v : ℝ) : Mark (raw G c) (Site c) := Mark.positions (native c) hearth v

lemma tag_coin (v : ℝ) (o : Site c) (L : List (raw G c)) : (Covariance.meterMark G c v).pay (L.map tag) o=
      (marked G c v).pay L o := by
  induction L with
  | nil => rfl
  | cons t l ih => rw [List.map_cons,Mark.pay,Mark.pay,ih]; rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma tag_jet (K : Directions G c → E) (L : List (raw G c)) (h : ContDiffAt ℝ L.length K B) :
    jet Covariance.atom K (L.map tag) B = jet (ray G c) (K ∘ paint G c) L ((paint G c).symm B) := by
  let U : Vec G c 1 →L[ℝ] Directions G c := (paint G c).toContinuousLinearMap
  let z := (paint G c).symm B
  have hh : U z=B := (paint G c).apply_symm_apply _
  have ht : ContDiffAt ℝ L.length K (U z) := hh.symm ▸ h
  rw [mark_map]; unfold jet
  change _=iteratedFDeriv ℝ L.length (K ∘ U) z _
  rw [WardBin.Lies.liner U ht, hh, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1; exact funext fun i => tag_map _

lemma tag_paid {Y : Config G c → Square (Key G f)}
    (h : Knew (Covariance.meterMark G c δ) (native c) (place S) Covariance.atom B k σ C η 1 (Y ∘ increment V)) :
    Knew (marked G c δ) (native c) (place S) (ray G c) ((paint G c).symm B) k σ C η 1 (SelectedOrderedKernels.over Y V) := by
  let e := paint G c; let z := e.symm B; let K := Y ∘ increment V
  have ht : ContDiffAt ℝ k K (e z) := (e.apply_symm_apply _).symm ▸ h.smooth
  refine ⟨ht.comp (f:=e) z e.contDiff.contDiffAt,?_,?_,?_⟩
  · simpa only [SelectedOrderedKernels.over,ContinuousLinearEquiv.apply_symm_apply, Function.comp_apply] using h.gap
  · simpa only [SelectedOrderedKernels.over,ContinuousLinearEquiv.apply_symm_apply, Function.comp_apply] using h.schur
  intro L hL hj
  have hp := h.jets (L.map tag) (by simpa) (by simpa)
  rw [tag_jet K _ (smooth_of_le h.smooth hj)] at hp
  refine ⟨⟨fun i=>?_⟩,⟨fun j=>?_⟩⟩
  · rw [← tag_coin]; exact hp.row.rows i
  rw [← tag_coin]; exact hp.col.rows j
end unified

variable (h : Covariance.Deck G p P x C r k σ b η i)
    (hS : S.patch=P) (hT : p.Funds S T) (hL : 100*(1+radiusB x) ≤ c.val)
    (hV : A.flags=RG.flags (temp x) V) (hB : ‖B‖≤r)

include h hS hT hL hV hB

lemma bought_here (F : Forest S.ratio) (s : S.Choices) (hδ : δ ≤ σ) :
    Knew (marked G c δ) (native c) (place S) (ray G c) ((paint G c).symm B) k σ C η 1 (SelectedOrderedKernels.over (fun U => AFull T A F x U s) V) :=
  tag_paid (Y:=fun U => AFull T A F x U s) (B70NonflatLogdetConnection.full_precision h T hS hT hL V s A F hV B hB hδ)

lemma active_pos (F : Forest S.ratio) (s : S.Choices) :
    (gram T x (increment V B) s (shots S x) A F).PosDef ∧ (fog A F T x (increment V B) s).PosDef := by
  let g := Sum.inl (α:=In x A F (G:=G)) (β:=vacant A F x G)
  obtain ⟨-,-,hq,ht,hr⟩ := h S T hS hT hL V s A F hV B hB
  have he := ht.definite
  rw [hr.eq_of_nhds] at he
  exact ⟨hq.submatrix (e:=g) Sum.inl_injective, he.submatrix (e:=g) Sum.inl_injective⟩

omit h hS hT hL hV hB
lemma advert (hs : 0<σ) (hc : 0≤C) (he : 0<η) (k : ℕ) :
    0 < faceBudget σ C η k ∧ faceBudget σ C η k ≤ σ := by
  let d := room σ C η k
  have H := room_grid hs hc he k
  have h : (4:ℝ)*(k+1:ℕ)*d ≤ σ := H.2.2.1.trans H.2.1
  have hD : d ≤ σ := (le_mul_of_one_le_left H.1.le (show 1 ≤ (4:ℝ)*(k+1:ℕ) from by push_cast; linarith [show (0:ℝ)≤k from by positivity])).trans h
  exact ⟨cash_pos k H.1, (cash_bounds k H.1).1.trans hD⟩

end YM.PhysicalNext.EndpointLoadF16.DetLong
