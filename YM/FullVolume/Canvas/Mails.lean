import YM.FullVolume.Canvas.Weather
/-! via Recurse plowed/support, Flex arcs everywhere. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open scoped Topology ContDiff BigOperators
variable {G: Gauge} {s: Sheet G}{L : Rolls s} {Θ : Protection L}{a:Levels G}{Z: ChartRatio G}
variable {w: Delays Θ} {y: Bar w}{v:Wait y}{V: Horizon a}{Q:PostCost L}
def haloB (A : Levels G)(m:ℕ)(R:PathData G):=R.Bounds (A.params m).clip (A.params m).width ((A.params m).paths*64) (64*A.clock.loopCap m)
def Skies {a:Levels G}(T':ℕ→Reel G)(i:ℕ)(Z:PathData G):=(T' i).Wing (a.S.side i) Z (a.params i).paths (a.clock.loopCap i)
structure MailBox {A:Levels G}(Y:Horizon A){Z:ChartRatio G}(Q : PostCost L)(T':ℕ→Reel G):Prop where
  step i : 1 ≤ A.clock.loopCap i
  vista i:(T' i).Price (A.params i).width
  planks i j: Bid.Larger (G:=G) (A.clock.op i j)
  glyph i : ∃ t c,(A.params i).width < t ∧ ∀ᶠ n in atTop,(Y.H n i).roots.strip t c
  resumes m N (h:m<N) (R:PathData G): haloB A (m+1) R→ Attached (Y.H N (m+1)) R →∃ D α ρ,Bubble Y Q Z N m R D α ρ∧ Skies (a:=A) T' m D
structure Inspected (U:Kin V Z)(Q:PostCost L)(T':ℕ→Reel G):Prop where
  sight : FullPaths U Q
  records m N (h:m<N): Bubble V Q Z N m (U.path N (m+1)) (U.path N m) (U.alpha N m) (U.stationary N m) ∧ Skies (a:=a) T' m (U.path N m)
lemma MailBox.expandR {T':ℕ→Reel G}(h:MailBox V Q T' (Z:=Z))(i:ℕ){R:PathData G}(hy:R.Bounds (a.params i).clip (a.params i).width (a.params i).paths (a.clock.loopCap i)):haloB a i R:=by
   have he:=le_mul_of_one_le_right (a.params i|>.paths_pos.le) (show 1≤(64:ℝ) by norm_num)
   have hp:= le_mul_of_one_le_left (zero_le_one.trans (h.step i)) (show 1≤(64:ℝ) by norm_num)
   refine { hy with rows:= fun x=>⟨(hy.rows x).1,(hy.rows x).2.1,(hy.rows x).2.2.trans he⟩, two:=⟨hy.two.1,hy.two.2.1,hy.two.2.2.trans hp⟩, three:=⟨hy.three.1,hy.three.2.1,hy.three.2.2.trans he⟩, four:=⟨hy.four.1,hy.four.2.1,hy.four.2.2.trans he⟩ }
lemma settled (T':ℕ→ Reel G) (h : Paid v a) (hl : ∀ i, 1 ≤ a.clock.loopCap i) (hp : ∀ N,∃ R : PathData G,BranchRow V N R)
    (hr : ∀ m N,m<N →∀ R, SatPath V N (m+1) R → ∃ D α ρ,Bubble V Q Z N m R D α ρ ∧ Skies (a:=a) T' m D) : ∃ T : Kin V Z, FullPaths T Q ∧ ∀ m N,m<N → Bubble V Q Z N m (T.path N (m+1)) (T.path N m) (T.alpha N m) (T.stationary N m) ∧ Skies (a:=a) T' m (T.path N m) := by
  classical
  have he (N n) (hN : n≤N) :
      ∃ Y : ℕ→PathData G,∃ α : ℕ→ℝ,∃ ρ : ∀ i,GainWire a i,BranchRow V N (Y N) ∧
        (∀ i,n ≤ i → i≤N → SatPath V N i (Y i)) ∧ ∀ i, n ≤ i → i < N → Bubble V Q Z N i (Y (i+1)) (Y i) (α i) (ρ i) ∧ Skies (a:=a) T' i (Y i) := by
    induction hN using Nat.decreasingInduction with
    | self =>
      obtain ⟨R,H⟩ := hp N
      refine ⟨fun _=> R,0,fun _ _ _ _=>0,H,fun i hi hu=> ?_,by intros; omega⟩
      rw [le_antisymm hu hi]; exact H.1
    | of_succ i hi I =>
      obtain ⟨Y,α,ρ,hY,he,H⟩ := I
      obtain ⟨D,w,θ,hD,h'⟩ := hr i N hi _ (he (i+1) le_rfl hi)
      refine ⟨update Y i D,update α i w,update ρ i θ,?_,?_,?_⟩
      · rw [update_of_ne hi.ne']; exact hY
      · intro m hm hv; rcases eq_or_lt_of_le hm with heq|heq
        · subst m; rw [update_self]; exact hD.lives
        rw [update_of_ne heq.ne']; exact he m (Nat.succ_le_of_lt heq) hv
      intro m hv hx; rcases eq_or_lt_of_le hv with heq|heq
      · subst m; rw [update_self,update_self,update_self,update_of_ne (by omega)]; exact ⟨hD,h'⟩
      rw [update_of_ne (by omega : m+1 ≠ i),update_of_ne (by omega : m≠i),update_of_ne (by omega : m ≠ i),update_of_ne (by omega : m≠i)]; exact H m heq hx
  choose Y α ρ H H' HI using fun N=> he N 0 (Nat.zero_le _)
  let V0 : Kin V Z := ⟨α,Y,ρ⟩; refine ⟨V0,⟨?_,fun N m h=> (H' N m (by omega) h).row,fun N m p F hm=> (HI N m (by omega) hm|>.1.steps p F).2.2.2.2⟩,fun m N h=> HI N m (Nat.zero_le _) h⟩
  refine ⟨h.stage.symm,h.lengths.symm,fun N m hm=> (H' N m (by omega) hm).ties,fun N m hm => (H' N m (by omega) hm).bound,
    fun N i=>(H N).2.1 i,fun N i=> (H N).2.2 i,fun N m p hm F=>(HI N m (by omega) hm|>.1.steps p F).1,
    fun N m p hm F=>?_,fun N m p hm F=> (HI N m (by omega) hm|>.1.steps p F).2.2.2.1,fun N m hm=> (HI N m (by omega) hm).1.earns,fun N m p hm F=> ?_⟩
  · exact ⟨(HI N m (by omega) hm|>.1.steps p F).2.1,(HI N m (by omega) hm|>.1.steps p F).2.2.1⟩
  exact higher_bill ((HI N m (by omega) hm|>.1.steps p F).2.2.2.2) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hl _) (Q.pos _).le) (Real.exp_pos _).le)

lemma verdant (G : Gauge) (hS : G.Simple) (B : MapPrices) (K : KernelChoices) (B₀ : ℕ→ℝ) (he : ∀ i, 0 ≤ B₀ i) (h : Fluent G) :
    ∃ σ A : ℕ→ℝ,(∀ i,0<σ i) ∧ (∀ i,0≤A i) ∧ ∀ (τ A' : ℕ→ℝ),τ ≤ σ → (∀ i,0<τ i) → A ≤ A' →
    ∃ (d γ : ℕ→ℝ) (u : ℕ→ℕ),(∀ i, 0≤d i) ∧ (∀ i,0<γ i) ∧ ∀ (s : Sheet G), s.kernel=K → Buys s τ A' d u B₀ →
      ∀ (L : Rolls s),∃ (V : ℕ →ℕ) (η : ℕ→ℝ), BudgetGap s L B η ∧ ∀ (Θ : Protection L),
        ∃ Δ : ℕ→ℝ, ∀ (D : Delays Θ) (T : Bar D) (M : Wait T), Δ≤D.betaEntry → V ≤ D.shells → ∀ (Q : PostCost L),Q.η=η → 1≤Q.Γ → Q.c ≤ γ →
        ∀ a : Levels G,Paid M a → ∀ X W : Horizon a, Craft.Rack a B X → Bid.Retained W X →
          ∀ Y : ChartRatio G,LocalRatio Y → ∃ (T':ℕ→ Reel G), MailBox (A:=a) (Z:=Y) W Q T' ∧ ∃ U : Kin W Y, Inspected U Q T'  := by
  obtain ⟨σ,A,hσ,hA,H,Q',hQ0,P⟩ := mastering G hS K B B₀ he
  let v i:=min (σ i) ((B.α i)/2)
  refine ⟨v,A,fun i=>lt_min (hσ i) (half_pos (B.alpha_pos i)),hA,fun τ A' ht hv hw => ?_⟩
  obtain ⟨d,y,u,F,W,h1,Lh⟩ := P τ (fun i=> A' i*64) hv (fun i=>mul_nonneg ((hA _).trans (hw _)) (by norm_num)) h
  refine ⟨d,fun i=> y i/2,u,fun i=>(h1 i).1,fun i=> half_pos (h1 i).2,fun s hs hB L => ?_⟩
  obtain ⟨η,H'⟩ := scene_gate L B
  choose V hT using fun i => waits_up (F i (L.L i)) (y i) 1 (h1 i).2 zero_lt_one
  refine ⟨fun i=> max (GateVolume i) (V i),η,H',fun Θ=> ?_⟩
  obtain ⟨Δ,hΔ⟩ := clocks G hS s L Θ (fun i=> W i (L.L i))
  refine ⟨Δ,fun w β b he hl Q hη hg hc a hd X Y hx hy Z HZ => ?_⟩
  have hw₀ := hΔ w β b he a hd
  have hpW i : (s.profile i).width ≤ σ i := (hB.fields i).1.trans_le ((ht i).trans (min_le_left ..))
  have hk i : A i ≤ (s.profile i).paths := (hw i).trans_eq (hB.fields i).2.symm
  have hg' i (n : Side) (hL': w.shells i ≤ n.val) : F i (L.L i) * Real.exp (-(y i)*n.val) ≤ Q.Γ i*Real.exp (-(Q.c i)*n.val) := by
    have hh : Q.c i ≤ y i/2 := hc i
    have hξ : 1≤Q.Γ i := hg i
    refine (hT i n ((le_max_right ..).trans ((hl i).trans hL'))).trans (mul_le_mul hξ (Real.exp_monotone (by gcongr)) (Real.exp_pos _).le (zero_le_one.trans hξ))
  let t i:=Q' (a.clock.J (i+1)) (a.clock.J i)
  have hM:MailBox Y Q t (Z:=Z):=by
     refine ⟨fun i=> (hw₀ i).2.2,fun i=> ?_, fun i p=> larger hd (fun i=> (le_max_left ..).trans (hl i)) i p,?_,?_⟩
     · have hy:=(hpW (a.clock.J i))
       have he :(a.params i)=s.profile (a.clock.J i) := by unfold Levels.params Calendar.params; rw [hd.stage]
       let k:= a.clock.J (i+1); let j:=a.clock.J i; have hm: k=j ∨ k=j+1:=by have h:j≤k:=a.fits.mono (Nat.le_succ _); have hh:k≤j+1:=a.fits.stepSlow _; omega
       rw [he]; have h:= hQ0 _ _ hm; exact ⟨lt_of_le_of_lt hy h.1,lt_of_le_of_lt hy h.2.1,lt_of_le_of_lt hy h.2.2⟩
     · intro i; let j:= a.clock.J i; refine ⟨B.α j,B.Ω j,?_, (eventually_gt_atTop i).mono fun n hn =>?_⟩
       · unfold Levels.params Calendar.params; rw [hd.stage]; exact lt_of_le_of_lt ((hB.fields j).1.le.trans ((ht j).trans (min_le_right ..))) (half_lt_self (B.alpha_pos _))
       rw [hy.1]; exact (hx.covers _ _ hn.le).2.2.2.1
     intro m N hN R hR hi
     unfold haloB at hR
     refine florentine hd (hη.symm ▸ H') (fun i=> le_trans (le_max_left ..) (hl i)) hg' hB.axis hpW hk hB.gradient hB.days HZ hx hy ?_ hw₀ hR hi hN
     rw [hs]; rw [funext fun i=> (hB.fields i).1,show (fun i=>(s.profile i).paths*64)=(fun i=> A' i*64) from funext (fun i=> by rw [(hB.fields i).2])]; exact Lh
  obtain ⟨U,H,U'⟩:=settled t hd hM.step (fun N=> budding hd hpW hk hB.axis hx hy H (fun i=>(hw₀ i).2.2) N) (fun m N hm R hR=> hM.resumes m N hm R (hM.expandR _ hR.bound) hR.ties)
  exact ⟨t,hM,U,H,U'⟩

end YM.Stationary
