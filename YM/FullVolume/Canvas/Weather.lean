import YM.FullVolume.Canvas.Flux
import YM.Next.STATIONARY.FullPlanned
/-! adapt Recurse supports with canonical reel history incl margin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G}
lemma Fluxed.preserves {S:Reel G} {Z W V X Y J Z' A D C s σ d α k C' d' u v g g' U U'} (h : Fluxed G J k Z W V X Y Z' A D C C' d s g S u U U') (hp : σ≤s) (hv : C' ≤ α) (he : d≤d') (ht : u ≤ v) (hz : g' ≤ g) {B B' : Side → ℝ} (hc : U≤ B) (hd : U'≤B') : Fluxed G J k Z W V X Y Z' A D C α d' σ g' S v B B' := by
  intro m n P H p q R F M Gx Gy GK b r c l hk hL hm hu hQ S hB hC hE
  obtain ⟨T,w,h1,h2,h3,h4,h5,h6⟩ := h m n P H p q R F M Gx Gy GK b r c l hk (ht.trans hL) hm hu hQ S hB hC hE
  exact ⟨T,w,h1,h2,fun s v w he hh hu hg hl=>h3 s v w he (hh.trans hp) (hv.trans hu) ((hd _).trans hg) hl,h4.trans he,h5,fun i j hp hx=> h6 i j ((hc _).trans hp) (hx.trans hz)⟩

structure Perform (G : Gauge) (P : MapPrices) (K : KernelChoices) (Z s A τ a d γ : ℕ →ℝ) (u : ℕ→ℕ)(Q:ℕ→ℕ→Reel G) (F W : ℕ → Side → ℝ) : Prop where
    moon (j i : ℕ) (h : j=i ∨ j=i+1) : Fluxed G K j (P.η j) (P.α j) (pacesE P j) (Z j) (P.α i) (pacesE P i) (Z i) (a j) (τ j) (A i) (d j) (s i) (γ j) (Q j i) (u j) (F j) (W j)

theorem mastering (G : Gauge) (hG : G.Simple) (K : KernelChoices) (P : MapPrices) (Z : ℕ→ℝ) (hZ : ∀ i,0 ≤ Z i) : ∃ s A : ℕ→ℝ,(∀ i,0<s i) ∧ (∀ i,0≤A i) ∧ BasesFine G P Z s A ∧ ∃ Zt : ℕ→ℕ→Reel G,(∀ j i,j=i∨j=i+1→ (Zt j i).Price (s i)) ∧ ∀ (τ C : ℕ→ℝ), (∀ i, 0<τ i) → (∀ i,0 ≤ C i) → Fluent G →
       ∃ (d γ : ℕ →ℝ) (u : ℕ→ℕ) (F W : ℕ→ Side→ℝ),(∀ i, 0≤d i ∧ 0< γ i) ∧ Perform G P K Z s A τ C d γ u Zt F W := by
  obtain ⟨b,E,H,H',H₀⟩ := beckon G P Z hZ
  obtain ⟨i⟩ := colorAvail G hG
  choose Q v w hv hw hq I using fun (j r : ℕ) => flux_cap G i hG K j (P.η j) (P.α j) (pacesE P j) (Z j) (P.α r) (pacesE P r) (Z r) (P.eta_pos j) (P.alpha_pos j) (paces_pos P j) (hZ j) (P.alpha_pos r) (paces_pos P r) (hZ r)
  let s (i) := min (b i) (min (w i i) (w (i+1) i))
  let A (i) := max (E i) (max (v i i) (v (i+1) i))
  have hx i j (h : j=i ∨ j=i+1) : s i ≤ w j i ∧ v j i ≤ A i := by
    obtain rfl|rfl := h; exact ⟨(min_le_right ..).trans (min_le_left ..),(le_max_left ..).trans (le_max_right ..)⟩; exact ⟨(min_le_right ..).trans (min_le_right ..), (le_max_right ..).trans (le_max_right ..)⟩
  refine ⟨s,A,fun i=>lt_min (H i) (lt_min (hw ..) (hw ..)),fun i=>(H' i).trans (le_max_left ..),?_,Q,fun i j d=> let H:= hq i j; let W: s j ≤ w i j := (hx j i d).1; ⟨lt_of_le_of_lt W H.1,lt_of_le_of_lt W H.2.1,lt_of_le_of_lt W H.2.2⟩,fun τ C hτ hC Y=>?_⟩
  · intro j m hm p hp B h hc hS he; obtain ⟨R,h₁,h₂,h₃,h₄,h₅⟩ := H₀ j m hm p hp B h hc hS he
    exact ⟨R,h₁,h₂,h₃,fun σ a Λ hu hs hf hg=> h₄ σ a Λ hu (hs.trans (min_le_left ..)) ((le_max_left ..).trans hf) hg, h₅⟩
  choose d c hd' F W hd hc h using fun (j i : ℕ) => I j i (τ j) (C j) (hτ j) (hC j) (Y _ _ _ _ _ _ (P.alpha_pos _) (P.eta_pos _) (paces_pos ..) (hZ _) (hτ _) (hC _))
  refine ⟨fun i=>max (d i i) (d i (i-1)),fun i=> min (c i i) (c i (i-1)),fun i=> max (hd' i i) (hd' i (i-1)),fun i x => max (F i i x) (F i (i-1) x),fun i x => max (W i i x) (W i (i-1) x),fun i=> ⟨(hd i i).trans (le_max_left ..),lt_min (hc i i) (hc i (i-1))⟩,?_⟩
  refine ⟨fun i j he=> Fluxed.preserves (h i j) (hx j i he).1 (hx j i he).2 ?_ ?_ ?_ ?_ ?_⟩
  all_goals
    rcases he with rfl|rfl <;> first
    | exact le_max_left ..
    | exact min_le_left ..
    | exact fun j=> le_max_left ..
    | (simp only [Nat.add_sub_cancel]; first|exact le_max_right ..| exact min_le_right ..| exact fun j=> le_max_right .. )

variable {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L}
section level
variable {Zc A σ d g : ℕ → ℝ} {u : ℕ → ℕ} {F T : ℕ → Side → ℝ} {Zt:ℕ→ℕ→Reel G} {m N : ℕ}
variable (h : Paid w a) (hΘ : BudgetGap s L P Q.η) (hS : ∀ i, GateVolume i ≤ W.shells i) (ht : ∀ i (n : Side),W.shells i ≤ n.val → F i (L.L i)*Real.exp (-(g i)*n.val) ≤ Q.Γ i*Real.exp (-Q.c i*n.val))
variable (hi : (fun i=> (s.profile i).clip.direct) ≤ Zc) (hw : (fun i=> (s.profile i).width) ≤ σ) (hA : A ≤ fun i => (s.profile i).paths)
    (hq : d ≤ fun i => (s.profile i).drift) (hp : u≤ s.floorL) (he : LocalRatio Z)
    (hb : Craft.Rack a P K) (hk : Bid.Retained V K) (hJ : Perform G P s.kernel Zc σ A (fun i=> (s.profile i).width) (fun i=> (s.profile i).paths*64) d g u Zt F T)
include h hΘ hS ht hi hw hA hq hp he hb hk hJ
lemma florentine (H : ∀ m,let j := a.clock.J (m+1); T j (L.L j) ≤ a.clock.loopCap m ∧ a.clock.loopCap (m+1)/2 ≤ a.clock.loopCap m ∧ 1 ≤ a.clock.loopCap m) {R : PathData G} (hy : R.Bounds (a.params (m+1)).clip (a.params (m+1)).width ((a.params (m+1)).paths*64) (64*a.clock.loopCap (m+1))) (hu' : Attached (V.H N (m+1)) R) (hm : m < N) :
    ∃ D α ρ,Bubble V Q Z N m R D α ρ ∧ let i:= a.clock.J (m+1); let j:= a.clock.J m; (Zt i j).Wing (a.S.side m) D (a.params m).paths (a.clock.loopCap m):= by
  let i:= a.clock.J m; let j:= a.clock.J (m+1); let U := a.params (m+1); let T' := a.params m
  let C := a.clock; let M:= (a.clock.op m 0).patch
  let p:= V.towers N m; let b := V.H N m; let z := V.H N (m+1)
  have hj : M.L=L.L j := (a.fits.sameFactor m).symm.trans (congr_fun h.lengths _)
  have h' : j=i ∨ j=i+1 := by
    have h : i≤j := a.fits.mono (Nat.le_succ m); have hi : j≤ i+1 := a.fits.stepSlow m; omega
  have hu : U=s.profile j := by unfold U Levels.params Calendar.params; rw [h.stage]
  have hT : T'=s.profile i := by unfold T' Levels.params Calendar.params; rw [h.stage]
  have hg v := larger h hS m v
  have hF := hull_fact hb hk hm; have hT' := hull_fact hb hk (le_of_lt hm)
  obtain ⟨h2,Ld⟩ := tack_columns hb hk hm
  let f := fun t => a.S.side m t; let c := fun t=> a.S.side (m+1) t
  have hv t (F : Forest (a.clock.op m t).ratio) := hΘ.ask j (a.clock.op m t) h.kernel hj rfl (hg t) F z b U.clip T'.clip R U.width (U.paths*64) _ _ _ _ p (Ld t) (hF.2.2.1 _) hy hu' (hF.2.2.2 t) (hT'.2.2.1 _)
  have hK t F := (hv t F).1
  choose ρ hρ using fun i F=> (hv i F).2
  let fF (t : ℕ) : Forest (a.clock.op m t).ratio := Classical.choice (Tree.select _ M.odd_side)
  let ξ : Armada f c M C.kernel := ⟨fun t=> (a.clock.op m t).sizes⟩
  let a' := fun i=> ρ i (fF i)
  have hZ : Fluxed G C.kernel j (P.η j) (P.α j) (pacesE P j) (Zc j) (P.α i) (pacesE P i) (Zc i) (U.paths*64) U.width (A i) (d j) (σ i) (g j) (Zt j i) (u j) (F j) (T j) := by rw [hu,show C.kernel=s.kernel from h.kernel]; exact hJ.moon j i h'
  have hΦ : Scud ξ G U.clip T'.clip R fF a' (P.α j) U.width (pacesE P j) (U.paths*64) (pacesE P j) (P.η j) (64*a.clock.loopCap (m+1)) (P.α i) (pacesE P i) (P.η i) z b p (Q.η j) :=
      ⟨hg, hF,hT',hu',hy,h2,Ld,fun t=> hK t _,fun i=> (hρ i _).1,fun i=>(hρ i _).2.1, fun i=>(hρ i _).2.2⟩
  obtain ⟨Y,α,hX,hY,hP,hE,hG,H'⟩ := hZ f c M ξ U.clip T'.clip R fF a' z b p (64*a.clock.loopCap (m+1)) (P.η i) (Q.η j) Z rfl (by rw [hj]; exact (hp j).trans (L.large j).need) (bound_climb G a m) (hu ▸ hi j) (hT ▸ hi i) hΦ (by linarith [(H (m+1)|>.2.2)]) (Q.price _) he
  obtain ⟨hy',hr,-⟩ := H m
  have hZ := hP T'.width T'.paths (a.clock.loopCap m) (a.params _).width_pos (hT ▸ hw i) (hT ▸ hA i) (by rw [hj]; exact hy') (by linarith only [hr])
  obtain ⟨hSat,hΩ⟩:=hZ
  refine ⟨Y,α,ρ, ⟨hE.trans (show d j ≤ U.drift from hu ▸ hq _), ⟨hX,hY,hSat⟩,fun t v => ⟨hK t v,(hρ t v).1, (hρ t v).2.1,?_,?_⟩⟩,hΩ⟩
  · exact Bid.one_for_all (a.clock.op m t) Work.F05.answer (hg t) (fF t) U.clip T'.clip R Y U.width (U.paths*64) _ _ (Q.price _) hy Z he (ρ t) (fun F=> (hρ t F).1) (hK t) (hG t) v
  have hn : W.shells j ≤ (f t).val := (Nat.le_mul_of_pos_right _ (by positivity)).trans (h.volume m t)
  have hr := transfer_bound (hg t) hy he (Q.price j) (hρ t v).1 (hρ t (fF t)).1 (hK t v) (hK t _) (H' (F j M.L) (g j) le_rfl le_rfl t)
  apply higher_bill hr
  simp only [mul_one]; rw [hj]; exact ht _ _ hn
end level
end YM.Stationary
