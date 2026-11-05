import YM.Next.UV_STRESS.Granular
import YM.UVNext.UV_STATION_TRANSFER.Cutoff


set_option warningAsError false

/-!
# Direct-to-Station

All demands through the fixed arity and weights on one lift.
We generalize the (mostly private) arithmetic in Vary/Granular to arbitrary
bases, reusable also in producing Granular from demands made with such bases.
Main result in this file: `direct_stations`. No PointLimits or Ordered or
ranks at all are needed to do the physical-to-test passage (of course still
need the converging physical hierarchy for applications TO that hierarchy;
this ordering can facilitate producing compatible prerequisites to it).
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.StationTransfer
open Function Set Filter MeasureTheory Metric Analysis Extraction
open Climb Ward Table Next.UVStress
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {D N n : ℕ} {t : Caps n}

section finance

variable {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℂ (E i)] [∀ i, FiniteDimensional ℂ (E i)]

abbrev Series {ι : Type} (E : ι → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] :=
  (i : ι) → Module.Basis (Fin (Module.finrank ℂ (E i))) ℂ (E i)

def draft (B : Series E) (j : Code E) (i : ι) := B i (j i)

def entry (B : Series E) (j : Code E) (v : (i : ι) → E i) := ∏ i, (B i).repr (v i) (j i)

variable [DecidableEq ι]
omit [∀ (i : ι), FiniteDimensional ℂ (E i)] in
lemma splits (v : (i : ι) → E i) (M : MultilinearMap ℂ E ℂ) (B : Series E) :
    M v = ∑ i : Code E, entry E B i v * M (draft E B i) := by
  have he : v = fun i => ∑ j, (B i).repr (v i) j • B i j := funext fun i => ((B i).sum_repr _).symm
  conv_lhs => rw [he]
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl; intro i _
  exact M.map_smul_univ _ _

lemma overall (B : Series E) : ∃ A : ℝ,0<A ∧ ∀ (v : (i : ι) → E i),
    (∑ j : Code E, ‖entry E B j v‖) ≤ A * ∏ i, ‖v i‖ := by
  let Z (j : Code E) i := LinearMap.toContinuousLinearMap ((B i).coord (j i))
  let T (j : Code E) := ∏ i, ‖Z j i‖
  refine ⟨(∑ j, T j)+1,add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ => by unfold T; positivity)) zero_lt_one,fun v => ?_⟩
  have hs (j : Code E) : ‖entry E B j v‖ ≤ T j * ∏ i, ‖v i‖ := by
    unfold T; rw [entry,norm_prod,← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => (Z j i).le_opNorm (v i)
  apply le_trans (Finset.sum_le_sum (fun i _ => hs i))
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
end finance

abbrev brand (C : Family G) (t : Caps n) i := (Bel C.book).Field (t i)

lemma errors_expand (W : Station C D) (hP : (Bel C.book).Smooth) (w : Ribbon (Bel C.book) t)
    (hu : ∀ i,t i≤D) (B : Series (brand C t)) (T : Test n) (N p : ℕ) :
    W.paid (hang t w) hu T N p - T.applyTo (disc (hang t w)) =
    ∑ j : record C t, entry (brand C t) B j w *
      (W.paid (hang t (draft _ B j)) hu T N p - T.applyTo (disc (hang t (draft _ B j)))) := by
  -- generalized from UV_STRESS/Granular
  let g j := draft (brand C t) B j
  let A (z : Ribbon (Bel C.book) t) := W.paid (hang t z) hu T N p
  let P (z : Ribbon (Bel C.book) t) := disc (hang t z)
  have ht : T.applyTo (P w)= ∑ j : record C t, entry _ B j w * T.applyTo (P (g j)) := by
    have he' : P w = fun x => ∑ j : record C t, entry _ B j w * P (g j) x :=
      funext fun x => splits _ _ ((Bel C.book).classMoment (Bel C.book) t x) _
    rw [he']; unfold Test.applyTo; simp_rw [Finset.mul_sum]
    have hp (j : record C t) (x : Points n) : T x * (entry _ B j w * P (g j) x)=entry _ B j w * (T x * P (g j) x) := by ring
    simp_rw [hp,← integral_const_mul]; exact integral_finsetSum _ fun j _ =>
      (T.smearing (smoothDisc (T:=Bel C.book) hP (hang t (g j))).continuousOn).const_mul _
  let T' := dilate W.rad T
  let M := (((C.S.a N : ℂ)^(4*n)) • ∑ r : Fin n → Lattice.Site (C.side N p), T' (Order.cells C N p r) • C.ensemble t r).compLinearMap
    fun i => (W.atCut (N,p) ⟨t i,Nat.lt_succ_of_le (hu i)⟩).toLinearMap
  have he (x : Ribbon (Bel C.book) t) : A x = M x := by
    simp only [M, MultilinearMap.compLinearMap_apply, _root_.smul_apply,_root_.sum_apply, smul_eq_mul]
    rfl
  change A w-T.applyTo (P w)=∑ j : record C t, entry _ B j w * (A (g j)-T.applyTo (P (g j)))
  simp_rw [mul_sub, Finset.sum_sub_distrib, ht,he]; rw [splits _ w M B]

/-- The operative basis prices do not request RA or smallness of scales.
No point interpolation needed here (feed from `from_balance` and
`short_word`, or with prices by other regulator argument). -/
def Watermark (W : ℕ → Station C D) (F : Extraction.Order) (R : ℝ) (u : ∀ i,t i≤D)
    (w : Ribbon (Bel C.book) t) :=
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ f : Test n, tsupport f ⊆ Scaling.window R n →
      ∀ M : ℝ, 0 < M → (∀ x, ‖f x‖ ≤ M) → F.upper
      (fun N p => ‖(W k).paid (hang t w) u f N p-f.applyTo (disc (hang t w))‖) (M*ε)

lemma across_water (W : ℕ → Station C D) {R : ℝ} (hP : (Bel C.book).Smooth)
    (hu : ∀ i,t i≤D) (B : Series (brand C t))
    (hv : ∀ j : record C t, Watermark W F R hu (draft _ B j)) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ k in atTop, ∀ w : Ribbon (Bel C.book) t, ∀ f : Test n, tsupport f ⊆ Scaling.window R n →
      ∀ M : ℝ, 0<M → (∀ x, ‖f x‖ ≤ M) → F.upper
      (fun N p => ‖(W k).paid (hang t w) hu f N p - f.applyTo (disc (hang t w))‖) (ε*Station.charge (hang t w)*M) := by
  obtain ⟨A,hA,hB⟩ := overall (brand C t) B
  classical
  have hp (j : record C t) := hv j (ε/A) (by positivity)
  filter_upwards [eventually_all.mpr hp] with k hk w f hf M hm hx η hη
  let b (j : record C t) := entry (brand C t) B j w
  let g := draft (brand C t) B
  let r := Station.charge (hang t w)
  let q (u : ℕ×ℕ) (v : Ribbon (Bel C.book) t) := (W k).paid (hang t v) hu f u.1 u.2 - f.applyTo (disc (hang t v))
  let L := ∑ j, ‖b j‖
  have hL : 0≤L := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  let δ := η/(1+L)
  have hd : 0 < δ := by unfold δ; positivity
  change ∀ᶠ i : ℕ×ℕ in F.fuse, ‖q i w‖ ≤ _
  have hq : ∀ᶠ i : ℕ×ℕ in F.fuse, ∀ j, ‖q i (g j)‖ ≤ M*(ε/A)+δ := eventually_all.mpr
    fun j : record C t => hk j _ hf M hm hx _ hd
  filter_upwards [hq] with i hi
  have hh : L*δ ≤ η := le_trans (mul_le_mul_of_nonneg_right (by linarith) hd.le)
    (show (1+L)*δ ≤ η from by unfold δ; rw [mul_div_cancel₀ _ (by linarith)])
  calc
    _ = ‖∑ j : record C t,b j * q i (g j)‖ := congr_arg norm (errors_expand _ hP w hu B ..)
    _ ≤ _ := (norm_sum_le ..).trans (by
      calc
        _ ≤ L*(M*(ε/A)+δ) := by
          unfold L; rw [Finset.sum_mul]; exact Finset.sum_le_sum (fun j _ => by rw [norm_mul]; gcongr; exact hi j)
        _ ≤ (A*r * (M*(ε/A))) + η := by rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_right (hB w) (by positivity)) hh
        _ = _ := by unfold r; field_simp)

/-- Make all finite basis demands before selecting the station. -/
lemma admissible_from_water (W : ℕ→Wheel C D) {a : (Bel C.book).RealSpin} (hP : (Bel C.book).Smooth)
    (h : RA W F a) {R ε : ℝ} (he : 0<ε)
    (hv : ∀ (n : ℕ) (_ : n≤N) (t : Caps n) (u : ∀ i,t i≤D), ∃ B : Series (brand C t),
      ∀ j : record C t, Watermark (fun k => (W k).toStation) F R u (draft _ B j)) :
    ∀ᶠ k in atTop, (W k).toStation.Admissible F a N R ε := by
  classical
  -- same finiteness as UV_STRESS/Granular
  have hp (n : Fin (N+1)) (t : Fin n → Fin (D+1)) := across_water (fun k => (W k).toStation) hP
    (t:=fun i : Fin n => (t i).val) (fun i => Nat.le_of_lt_succ (t i).isLt) _
    ((hv n (Nat.le_of_lt_succ n.isLt) (fun i : Fin n => (t i).val) _).choose_spec) _ he
  filter_upwards [h.grants,h.central,h.real,h.h_symm,eventually_all.mpr fun n => eventually_all.mpr (hp n)] with i hi hc hr hx hh
  refine ⟨hi,hc,hr,hx,fun {n} hu v hu' => ?_⟩
  let b : Fin (N+1) := ⟨n,Nat.lt_succ_of_le hu⟩
  let t (i : Fin n) : Fin (D+1) := ⟨(v i).1,Nat.lt_succ_of_le (hu' i)⟩
  exact hh b t (fun j => (v j).2)

lemma direct_admissible (W : ℕ→Wheel C D) (a : (Bel C.book).RealSpin)
    (hC : C.Makes) (hm : (Bel C.book).Smooth) {R ε : ℝ} (hr : 0<R) (he : 0<ε)
    (h : Granular W F a N R) : ∀ᶠ k in atTop, (W k).toStation.Admissible F a N R ε := by
  apply admissible_from_water W hm h.toRA he
  intro n hn t hu
  let B (i : Fin n) := Module.finBasis ℂ (brand C t i)
  refine ⟨B,fun j => ?_⟩
  obtain ⟨e,A,P,hP⟩ := h.proof_ n hn t hu j
  exact short_word W hu _ hm hr (from_balance W (depthWord t j) hC hm hr hP)

/-- Strengthened producer adapter: no physical PointLimits or Ordered
or Smooth needed. Entirely regulator comparison to fixed free kernel. -/
theorem direct_stations (hC : C.Makes) (hm : (Bel C.book).Smooth) (a : (Bel C.book).RealSpin)
    (estimate : ∀ (N D : ℕ) (R : ℝ), 1 ≤ R → ∃ W : ℕ → Wheel C D, Granular W F a N R) : Stations C F a where
  arbitrarily D N R ε δ hr he hd := by
    obtain ⟨W,hW⟩ := estimate N D R hr
    obtain ⟨k,hk,hK⟩ := ((direct_admissible W a hC hm (by linarith) he hW).and (hW.small.eventually (ge_mem_nhds hd))).exists
    exact ⟨(W k).toStation,hk,hK⟩

end YM.UVNext.StationTransfer
