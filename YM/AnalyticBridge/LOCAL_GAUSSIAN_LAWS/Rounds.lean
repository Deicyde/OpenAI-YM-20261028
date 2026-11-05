import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.PatchJet
import YM.Next.SCHEDULE.Postal
import YM.Push.CUTOFF_PROJECTORS.Signed
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stencils

/-!
# Remote authorized jets compared *as_linear_operators* with flat ones

Fixed L, all signed channels with shifts using U (pipeline at the common
jolt). Sufficient hypotheses on positive bond reads in the gauge being
actually tested. Need not be same gauge when *tail terms* prove small
but near comparison uses ONE. The base for the present cost is a coarse
site; fine inputs use parent. Direction compact support only for pricing
the inChannel law; stencil alone suffices for the origin lies derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Remote
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows SectorNext.Remainder.Affine Push.SectorMeasure  Oriented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma unit_walk (G : Gauge) (p : Site n) (w : Walk) : travel (1:Config G n) p w=1 := by
  induction w generalizing p <;> simp_all [travel,Step.read]
lemma travel_neutral (x : Config G n) (t : ℝ) (h : ∀ i, G.chord (x i) ≤ t) (p : Site n) (w : Walk) :
    G.chord (travel x p w) ≤ w.length * t := by
  have he := travel_bound t w p x (1:Config G n) (fun i _ => by simpa using h i)
  simpa only [unit_walk G, inv_one,mul_one] using he
lemma angles (s : Signed) (p : Directions G n) (x : Config G n) : ‖inChannel s x p‖ ≤ ‖p‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => (in_size s x p i).le.trans (norm_le_pi_norm p _)

def paid (S : StepData c f) (U : Config G f) (o : Site c) (D : ℕ) (t : ℝ) :=
  ∀ e : Bond f, separation o (S.ratio.parent e.1) ≤ D → G.chord (U e) ≤ t

def invoice (S : StepData c f) (a : Directions G f) (o : Site c) (D : ℕ) :=
  ∀ e : Bond f, ¬ separation o (S.ratio.parent e.1) ≤ D → a e=0
lemma in_paid (s : Signed) {U : Config G f} {o : Site c} {D : ℕ} {a : Directions G f} {t : ℝ}
    (h : paid S U o D t) (hv : invoice S a o D) (ht : 0≤t) :
    ‖inChannel s U a - inChannel s 1 a‖ ≤ 2*G.colorScale*t*‖a‖ := by
  refine (pi_norm_le_iff_of_nonneg (by have hh := G.colorScale_pos; positivity)).mpr fun i => ?_
  rw [Pi.sub_apply,in_eval,in_eval]; split
  next he =>
    let b := sendEdge s (0:Site f) i
    rw [LinearMap.neg_apply,LinearMap.neg_apply, Pi.one_apply, inv_one,G.adjoint_one]
    rw [show -(G.adjoint _ _) - -(a b) = - (G.adjoint _ _ - a b) by abel,norm_neg]
    by_cases hh : separation o (S.ratio.parent b.1) ≤ D
    · have hz := ad_change (a b) (U b)⁻¹ 1
      rw [G.adjoint_one,inv_one,mul_one,G.chord_inv] at hz
      have hx : 0≤ 2*G.colorScale := by have := G.colorScale_pos; positivity
      exact hz.trans (mul_le_mul (mul_le_mul_of_nonneg_left (h _ hh) hx) (norm_le_pi_norm a _) (norm_nonneg _) (mul_nonneg hx ht))
    rw [hv b hh,map_zero,sub_zero,norm_zero]; have hh := G.colorScale_pos; positivity
  simp only [sub_self,norm_zero]; have hh:=G.colorScale_pos; positivity

lemma angles_paid (s : Signed) {U : Config G f} {o : Site c} {D : ℕ} {t : ℝ}
    (h : paid S U o D t) {p : Site c} (e : Bond f)
    (he : separation o (s.act p) + separation p (S.ratio.parent e.1)+1 ≤ D) : G.chord (pull s 0 U e) ≤ t := by
  let i := sendEdge s (0:Site f) e
  have hx := spin_separation (S:=S) e s p
  have hw := separation_triangle o (s.act p) (S.ratio.parent i.1)
  have hh := h i (by change separation (s.act p) (S.ratio.parent i.1)≤_ at hx; omega)
  rw [turn_read]; split
  · rw [G.chord_inv]; exact hh
  exact hh

lemma travels_paid (s : Signed) {U : Config G f} {o : Site c} {D : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (h : paid S U o D t) (p : Site f) (w : Walk)
    (he : separation o (s.act (S.ratio.parent p)) + w.length+1 ≤ D) :
    G.chord (travel (pull s 0 U) p w) ≤ w.length*t := by
  let z:=S.ratio.parent p
  let x : Config G f := fun i => if separation z (S.ratio.parent i.1) ≤ w.length then pull s 0 U i else 1
  rw [travel_near S.ratio.parent (Work.E03.parent_step S) (pull s 0 U) x p w w.length le_rfl (by
    intro i hi; unfold x; rw [if_pos hi])]
  apply travel_neutral x t
  intro i; unfold x; split
  next hx => exact angles_paid s h i (p:=z) (by unfold z at *; omega)
  rw [G.chord_one]; exact ht

set_option maxHeartbeats 320000 in
lemma remote_authorized (G : Gauge) (P : Patch) (K : KernelChoices) (hp : P.Branches K G) :
    ∃ A δ : ℝ, 0≤A ∧ 0<δ ∧ ∀ t : ℝ, 0≤t → t≤δ → ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ (o : Site c) (D : ℕ) (V : Config G c) (s : Signed) (a : Directions G f),
    paid S (replica S.ratio V) o D t → invoice S a o D →
    (∀ i : Cell f, separation o (s.act (S.ratio.parent i.1))+5 ≤ D →
      ‖plaquetteJet S V s i a-plaquetteJet S 1 s i a‖ ≤ A*t*‖a‖ ∧
        ‖plaquetteJet S (1:Config G c) s i a‖ ≤ A*‖a‖) ∧
    (∀ (k : S.Choices) (i : Bond c), separation o (s.act i.1)+predReach P+1 ≤ D →
      ‖blockJet V k s i a - blockJet (1:Config G c) k s i a‖ ≤ A*t*‖a‖ ∧
        ‖blockJet (1:Config G c) k s i a‖ ≤ A*‖a‖) := by
  obtain ⟨A,δ,hA,hδ,H⟩ := both G P K hp
  let M:=A*(1+2*G.colorScale); have hs:=G.colorScale_pos
  refine ⟨M,δ,by unfold M; positivity, hδ,?_⟩; intro t ht he c f S hP hK o D V s a hw hv
  let V' := replica S.ratio V
  let U := pull s (0:Site f) V'; let v := inChannel s V' a; let v0 := inChannel s 1 a
  have hh := H t ht he S hP hK U
  have h1 := H 0 le_rfl hδ.le S hP hK (1:Config G f)
  have hx (e : Bond f) : G.chord ((1:Config G f) e) ≤ 0 := by simp [G.chord_one]
  have hQ : M≥A := by unfold M; nlinarith
  have H0 (E W : Directions G f →L[ℝ] G.Color) (hh : ‖E-W‖ ≤ A*t) (hh' : ‖W‖ ≤ A) :
      ‖E v-W v0‖ ≤ M*t*‖a‖ ∧ ‖W v0‖ ≤ M*‖a‖ := by
    have h' : ‖E v-W v‖ ≤ A*t*‖a‖ := ((E-W).le_opNorm _).trans (mul_le_mul hh (angles s a V') (norm_nonneg _) (mul_nonneg hA.le ht))
    have h'' : ‖W v-W v0‖ ≤ A*(2*G.colorScale*t*‖a‖) := by
      rw [← map_sub]; exact (W.le_opNorm _).trans (mul_le_mul hh' (in_paid s hw hv ht) (norm_nonneg _) hA.le)
    rw [show E v-W v0=(E v-W v)+(W v-W v0) by abel]
    exact ⟨(norm_add_le ..).trans ((add_le_add h' h'').trans_eq (by unfold M; ring)),
      (W.le_opNorm _).trans (mul_le_mul (hh'.trans hQ) (angles s a _) (norm_nonneg _) (hA.le.trans hQ))⟩
  have hV : pull s (0:Site f) (replica S.ratio (1:Config G c))=1 := by funext i; rw [turn_read,replica_one]; split <;> simp
  constructor
  · intro i hi
    obtain ⟨hp,hh,ht⟩ := hh.1 i (fun e h => angles_paid s hw e (p:=S.ratio.parent i.1) (by omega))
    have hl (Z : Config G c) (hZ : ContDiffAt ℝ ω (pTest (pull s 0 (replica S.ratio Z)) i) 0) := (plaquette_turn s Z i hZ).2 a
    unfold plaquetteJet; rw [hl V hp, hl (1:Config G c) (by rw [hV]; exact (h1.1 i (fun e _ => hx e)).1),hV,replica_one]
    exact H0 _ _ hh ht
  intro k i hi
  obtain ⟨hp,hh,ht⟩ := hh.2 (choice s k) i (fun e h => angles_paid s hw e (p:=i.1) (by omega))
  have hl (Z : Config G c) (hZ : ContDiffAt ℝ ω (bTest (pull s 0 (replica S.ratio Z)) (choice s k) i) 0) := (block_turn s Z i k hZ).2 a
  unfold blockJet; rw [hl _ hp, hl 1 (by rw [hV]; exact (h1.2 _ _ (fun e _ => hx e)).1),hV,replica_one]
  exact H0 _ _ hh ht
end YM.AnalyticBridge.LocalGaussianLaws.Remote
