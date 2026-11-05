import YM.RG08.Ward.Mall
/-! # Exposing symmetry in slice charts, not leaving out reflections.
Transport may depend on pulse, not on which subintegrals are being evaluated. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles
open PertExtension.Series.Tested
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f n : Side} (S : StepData c f) {G : Gauge} (T : Forest S.ratio)
variable {κ : S.Choices} {V : ℕ → Config G f → ℝ} {v w : ℝ → Link G c} {k : ℕ} {X : Type} {ℓ : Filter X}
    {x : X→Config G f} {b : X→Site f→G.El}
local notation "Θ[" t "]" => discPay S G T t κ k V
local notation "P" => (T.Slice G)
local notation "Φ" => (𝓝 ((0:ℝ),(1:P)))
local notation "A" => ℝ×P
local notation "β" => 𝓝 (1:Config G f)
def bayExit (e : ℝ → Config G f≃ₜConfig G f)(p : A) := e p.1 (T.drape p.2)
def Opinion (κ : S.Choices) (V : ℕ→Config G f→ℝ) (k : ℕ) (v w : ℝ→ Link G c) :=
    ∃ e : ℝ→((P)≃ₜ(P)), (Tendsto (fun p:A=> e p.1 p.2) Φ (𝓝 1)) ∧
      (Tendsto (fun p:A=> (e p.1).symm p.2) Φ (𝓝 1)) ∧ (∀ t,MeasurePreserving (e t) (T.order G) (T.order G)) ∧
      ∀ᶠ p:A in Φ, discPay S G T v κ k V p.1 p.2= discPay S G T w κ k V p.1 (e p.1 p.2)

lemma architect (h : S.patch.Branches S.kernel G) (hW : ∀ i,Pointwise (V i ∘ input G f)) (e : ℝ→(Config G f≃ₜConfig G f))
    (hy : Tendsto (bayExit S T e) Φ β) (ht : Tendsto (bayExit S T (fun t=> (e t).symm)) Φ β)
    (hb : ∀ t, MeasurePreserving (e t) (prior G f) (prior G f)) (hz : ∀ t, Cart G T (e t)) (he : ∀ t,Cart G T (e t).symm)
    (hh : ∀ᶠ p:A in Φ, laboratory S κ k V p.1 (input G c (p.1 • w p.1)) (bayExit S T e p)= laboratory S κ k V p.1 (input G c (p.1 • v p.1)) (T.drape p.2)) :
    Opinion S T κ V k v w := by
  let E t:= carriage G T _ (hz t) (he t); have hp : Tendsto (Profiles.wick T) β (𝓝 1) := by rw [← wick_b G T]; exact (continuous_wick T).tendsto _
  refine ⟨E,hp.comp hy,hp.comp ht,fun t=> preserving G T _ (hb t) _ _,?_⟩
  have hi:= wipe_fee S T hy h hW (κ:=κ) (R:=fun p:A=> input G c (p.1 • w p.1)) (t:=Prod.fst) (k:=k)
  filter_upwards [hh,hi] with x hx hv; exact congr_arg (fun v:ℝ=> Real.exp (-v/x.1^2)) ((hv.trans hx).symm)
lemma baySimp : Tendsto (fun p:A=> T.drape p.2) Φ β := by
  let p:A:=((0:ℝ),1); have h : Tendsto T.drape (𝓝 p.2) β := (drape_b G T) ▸ (T.continuous_drape.tendsto p.2)
  exact h.comp (continuous_snd.tendsto p)
lemma signed_vote (s : Signed) (h : S.patch.Branches S.kernel G) (hW : ∀ i,Pointwise (V i ∘ input G f))
    (hv : ∀ᶠ t in 𝓝 (0:ℝ),input G c (t • w t)=pull s 0 (input G c (t•v t))) : Opinion S T κ V k v w := by
  let e:= signedWalk G f s; let P' p:=T.drape (p:A).2
  have he (s : Signed) : Tendsto (pull (K:=G.El) (R:=Per f) s 0) β β := by simpa only [show pull s 0 (1:Config G f)=1 from by funext i; simp [rerun]] using (continuous_pull s (0:Site f)).tendsto (1:Config G f)
  have hx : Tendsto P' Φ β:= baySimp S T
  refine architect S T h hW (fun _=> e) ((he s).comp hx) ((he s⁻¹).comp hx) (fun _=> prior_pull ..) (fun _=> signed_cart G T s) (fun _=> signed_cart G T s⁻¹) ?_
  let i:= S.withinChoice s 0 κ; let Q p:= pull s 0 (P' p)
  have hi := hx.eventually (Work.F04.prediction_germ (S:=S) h i κ)
  filter_upwards [hi,(continuous_fst.tendsto ((0:ℝ),(1:P))).eventually hv,
    (eventually_all_finset (Finset.range (k+2+1))).mpr (fun j _=> spin_force (hW j) Φ hx s)] with x he hV hd
  let U:=input G c (x.1 • v x.1); have hs:S.ratio.embed 0=0:=map_zero S.ratio.root
  have hz:= S.prediction_channel h s 0 (P' x) κ; rw [hs,show S.prediction (P' x) (S.withinChoice s 0 κ)=_ from he] at hz
  rw [hV]; unfold laboratory; change tickets S _ (S.prediction (Q x) _)+_=_
  rw [show S.prediction (Q x) κ=_ from hz,ticket_spin]; congr 1; exact Finset.sum_congr rfl fun j hj=> congr_arg _ (hd j hj)

lemma gaugeOpinion (h : S.patch.Branches S.kernel G) (hW : ∀ i,Pointwise (V i ∘ input G f)) (d : ℝ→ Site c→G.El)
    (z : G.El) (hz : Tendsto d (𝓝 0) (𝓝 (fun _=>z))) (he : ∀ᶠ t in 𝓝 0, input G c (t•w t)= Lattice.gauge (d t) (input G c (t•v t))) : Opinion S T κ V k v w := by
  let f' t:= d t ∘ S.ratio.parent; let e t:= gaugeWalk G (f' t); let i t: Site f→G.El:=(f' t) * fun _=>z⁻¹; let U p:= T.drape (p:A).2
  have hx : Tendsto U Φ β:= baySimp S T; have hu : Tendsto Prod.fst Φ (𝓝 0):=continuous_fst.tendsto ((0:ℝ),(1:P))
  have hh : Tendsto (fun p:A=> f' p.1) Φ (𝓝 (fun _=>z)) := tendsto_pi_nhds.mpr (fun j=> tendsto_pi_nhds.mp (hz.comp hu) (S.ratio.parent j))
  have hw {q : G.El} {i : A→ (Site f→ G.El)} (h : Tendsto i Φ (𝓝 (fun _=>q))) : Tendsto (fun p:A=> Lattice.gauge (i p) (U p)) Φ β :=
    tendsto_pi_nhds.mpr fun j=> by
      have hv := ((tendsto_pi_nhds.mp h j.1).mul (tendsto_pi_nhds.mp hx j)).mul ((tendsto_pi_nhds.mp h (j.1+step j.2)).inv)
      simpa using! hv
  let Y:= bayExit S T e
  have hF : Tendsto Y Φ β:=hw hh; have hX := hw (i:= fun p=> fun _=>z) tendsto_const_nhds
  have hg : Tendsto (fun p:A=> i p.1) Φ (𝓝 1) := by
    have hp :(fun q':Site f=>z)*(fun _=>z⁻¹)=1 := funext fun _=>mul_inv_cancel z
    exact hp ▸ hh.mul (g:=fun _=> (fun _=>z⁻¹)) tendsto_const_nhds
  have hl (p:A) : Lattice.gauge (i p.1) (Lattice.gauge (fun _=>z) (U p))=Y p := by
    funext x; change _ = Lattice.gauge (f' p.1) _ x; simp only [Lattice.gauge,i, Pi.mul_apply]; group; rfl
  have hy t : Cart G T (e t).symm := by -- gaugeWalk inverse coordinate defeq pointwise double inv
    intro k h v; exact gauge_cart G T (f' t)⁻¹ k h v
  refine architect S T h hW e hF (hw (q:=z⁻¹) hh.inv) (fun t=> prior_gauge _) (fun t=> gauge_cart G T _) hy ?_
  filter_upwards [(eventually_all_finset (Finset.range (k+2+1))).mpr (fun j _=> (hue_force (hW j) Φ hx z).and (gauge_force (hW j) _ hX hg)),hu.eventually he] with x hp H
  unfold laboratory; rw [H]; change tickets S _ (S.prediction (Y x) κ)+_ = _
  have ht : d x.1 = f' x.1 ∘ S.ratio.embed := funext fun _=> by unfold f'; simp [S.ratio.embed_parent]
  rw [ht, show S.prediction (Y x) κ = S.prediction (Lattice.gauge (f' x.1) (T.drape x.2)) κ from rfl,shield_k S h]; congr 1; refine Finset.sum_congr rfl fun j hj=> ?_
  refine congr_arg (x.1^(2*j)* ·) ?_; change V j (Y x)= V j (U x); rw [← hl]; exact (hp j hj).2.trans (hp j hj).1
end YM.RG08.Reflect
