import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inc
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Lakeside

/-!
# Speck short germ. Use a local chart only at the true footprint
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica.Clutch
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {a α β γ d η σ W s b μ : ℝ} {j : ℕ}
open Brush
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {V : E → Config G c} {y : E→ Directions G f} {w : E→ Air f G}

private lemma billpack (p : Room P S T X.x) (h : Clutch X z a β s x j V y w) (hp : Mode V x j d) (H : X.manifest)
    (i : Stream c f) (hk : ¬ Inside (rowSite S i) X.seeds (200*X.B)) (hψ : ¬ (fun k=> X.enforce (2*a) (y k) (X.booth (rowSite S i)))=ᶠ[𝓝 x] fun _=>0) :
    let K:= i.1; let _o := rowSite S i; let v t:=vary X (V t)
    let U:= X.input (worldZ X β z); let Z t:=pull K 0 (V t)
    let A k:= displacement K ((v k).signal (y k)) (replica S.ratio (V k)); let m:=7*X.B/8; let p:=s+4*a*X.t
    let F:= royalty G*(p*royalty G)
    Clean ((fun y=>pull K 0 (V y)) x) X.x (lead S i.2) (m+1) ∧
      (∀ j', distAt S j' (lead S i.2) ≤ m → Brush j (F*(1+(d+1+d))^j) 1 (fun k=>A k j') x) ∧
      (∀ᶠ k in 𝓝 x, AgreeNear S.ratio.parent (lead S i.2) m (pull K 0 U) (increment (replica S.ratio (Z k)) (A k))) ∧
      ∀ k, rootface (v k) (y k) U true K i.2= squarepot T X.x (choice K X.k) (pull K 0 U) (Z k) (A k) i.2 := by
  intro K o v U Z A m u B
  have he : 100 ≤ X.B := p.sight.1; have hM := h.pulse
  obtain ⟨hv,hq⟩ := darling h _ hψ
  have hh q (hi : distAt S q o≤ X.B) : q∉F.trunks → X.Hot q := fun hz=> far_active X.seeds F q (clear hk (by unfold distAt o at hi; omega)) hz
  have ho : ¬ Inside o X.seeds X.B := clear hk (by change X.B+separation o o≤_; rw [separation_self]; omega)
  refine ⟨?_,?_,?_,?_⟩
  · dsimp only; rw [h.atV]; exact ((clean_far X.seeds X.V H ho).shrink (v:=o) (D:=m+1) (by rw [separation_self]; unfold m; omega)).turn
  · intro i' hI
    have hz : distAt S (Channel.edge K i') o ≤ X.B := (projects S K (lead S i.2) i').trans (by unfold m at hI; omega)
    have hF : Brush j u 1 (fun k=> (v k).signal (y k) (edge K i')) x := by
      by_cases ht:edge K i'∈F.trunks
      · simp_rw [(v _).on_trunk _ _ ht]; apply (Brush.certified zero_le_one (0:G.Color)).climb _ le_rfl
        have hp:=h.price; rw [norm_zero]; unfold u; nlinarith only [hp,hM]
      have hk:∀ k, (v k).Hot _ := fun k=> hh _ hz ht
      simp_rw [(v _).at_hot _ _ (hk _)]; exact hv _ (X.ages _ _ (hh _ hz ht) hz)
    exact (displacement_pay (S:=S) K i' u _ hp hF).trim
  · filter_upwards [hq] with k hY
    have hp q (ht : distAt S q o ≤ X.B) : U q=increment (replica S.ratio (V k)) ((v k).signal (y k)) q := by
      by_cases hq : q∈ F.trunks
      · unfold U; rw [X.sliced _ q hq, increment,(v k).on_trunk _ _ hq,G.mat_lieExp_zero,one_mul]; exact
          (if_pos (F.trunk_internal (by simpa using hq))).symm
      have he:= hh q ht hq
      change X.input _ q=_; rw [← hY q (X.ages _ _ he ht),(v k).viewing _ q he]; unfold increment; rw [(v k).at_hot _ _ he]; rfl
    unfold Z A; rw [← pulls_replica,← pull_increment]
    exact Zone.nearU S K (fun q hF=> hp q (hF.trans (by unfold m; omega)))
  intro k
  unfold rootface squarepot; refine congrArg₂ (·-·) rfl ?_
  apply sum_congr rfl; intro p hp
  have hx : (v k).selected K (spot S p) := by
    rw [(parent_iff (S:=S) ..).mp hp]
    exact
      clear hk (by change 6*X.B+separation o o ≤_; rw [separation_self]; omega)
  rw [Blaze.Vine.pot,if_pos hx]; rfl

lemma star_earth (P : Teller G) (L : Side) (D : Patch) (hd : D.Branches P.bind G) (j : ℕ) (a : ℝ) {p q : ℝ→ℝ}
    (h : Rate G L (-(1/2)) p) (hp : Rate G L (-(1/2)) q) (hv : ∀ᶠ x in atTop, 0≤ p x) :
    ∃ C, Rate G L (-(3/2)) C ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S:StepData c f) (T:Tube G S), S.patch=D → Works P L x S T →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (V:E→ Config G c) (y:E) (F:Forest S.ratio) (X: Coat T F) (z : Air f G)
      (β : ℝ) (U : E→ Directions G f) (w:E→ Air f G), X.x=x → X.manifest → Mode V y j (p x) → Clutch X z a β (q x) y j V U w →
        ∀ i : Stream c f, ¬Inside (rowSite S i) X.seeds (200*X.B) →
        (¬ (fun y=> X.enforce (2*a) (U y) (X.booth (rowSite S i)))=ᶠ[𝓝 y] fun _=>0) →
        Brush j (C x) 1 (fun k=> rootface (vary X (V k)) (U k) (X.input (worldZ X β z)) true i.1 i.2) y := by
  let g:= royalty G
  let f x:= g*((q x+4*a*Pressure.fiery G x L)*g) * (1+(p x+1+p x))^j; let Q x:=p x+|f x|
  have hA:=Rate.const (G:=G) (L:=L) (1:ℝ)
  have hh:= h.weaken (b:=0) (by norm_num)
  have hf : Rate G L (-(1/2)) f := by
    simpa only [zero_mul,add_zero] using!
      ((((hp.add (Rate.flame.mul_left (4*a))).mul_right g).mul_left g).mul ((hA.add ((hh.add hA).add hh)).pow j))
  obtain ⟨C,hC,hT⟩:= Frond.earth P L D hd j (h.add (hf.compare (v:=fun x=> |f x|) (Eventually.of_forall fun x=> (abs_abs _).le)))
    (hv.mono fun i hi=>add_nonneg hi (abs_nonneg _))
  refine ⟨C,hC,?_⟩
  filter_upwards [room G P L,hT] with x hT hx c f S T hS ht E _ _ V y F X z β U w hX hp hM H i hr hm
  subst x
  obtain ⟨h₁,h₂,h₃,h₄⟩:= billpack (hT _ _ S T ht) H hM hp i hr hm; dsimp only at h₁ h₂ h₃ h₄
  simp_rw [h₄];
  have hp : p X.x ≤ Q X.x := le_add_of_nonneg_right (abs_nonneg _)
  exact hx _ _ S T hS ht (choice i.1 X.k) i.2 E (fun y=> pull i.1 0 (V y)) _ _ y
    ⟨hM.pos.trans hp,fun i'=> ((Blaze.turn hM i.1).atLink i').climb le_rfl hp⟩ h₁ (fun i h=> (h₂ i h).climb (by
      unfold Coat.t; rw [ht.length_eq]; exact (le_abs_self _).trans (le_add_of_nonneg_left hM.pos)) le_rfl) h₃
end YM.ConnectedActivityE6.Blaze.Silica.Clutch
