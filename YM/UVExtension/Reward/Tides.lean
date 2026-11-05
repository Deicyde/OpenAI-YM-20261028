import YM.UVExtension.Reward.AtLimit


/-! Every one-step limit reached, comparison modulo the vanishing waveform.
Coincidences at finite stage not assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Reward
open Lattice RG Supply Stationary Projection Precision Bloch Laurent Exterior Wilson Tree Filter Function Finset MenuView
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} {s : Sheet G} {L : Rolls s} {Θ : Protection L} {a : Levels G} {P : MapPrices} {K V : Horizon a} {Z : ChartRatio G} {W : Delays Θ} {y : Bar W} {w : Wait y} {Q : PostCost L} {D : Knobs a} {ε : ℝ} {m N :ℕ}


def Each (V:Horizon a)(D:Knobs a)(Q:PostCost L)(Z:ChartRatio G)(ε:ℝ)(m N:ℕ)(R U:PathData G)(α:ℝ)(ρ:GainWire a m) := ∃ x, sat D V N m x=U ∧ Courtesy V D Q Z ε N m R x α ρ
lemma fieldArray (h : Paid w a) (hl : ∀ i, 1 ≤ a.clock.loopCap i) (hp : ∀ N,∃ R : PathData G,BranchRow V N R)
    (hr : Mints D P V Q Z ε) : ∃ T : Kin V Z, FullPaths T Q ∧ ∀ N m,m<N→ Each V D Q Z ε m N (T.path N (m+1)) (T.path N m) (T.alpha N m) (T.stationary N m) := by
  classical
  have he (N n) (hN : n≤N) :
      ∃ Y : ℕ→PathData G,∃ α : ℕ→ℝ,∃ ρ : ∀ i,GainWire a i,BranchRow V N (Y N) ∧
        (∀ i,n ≤ i → i≤N → SatPath V N i (Y i)) ∧ ∀ i, n ≤ i → i < N → Each V D Q Z ε i N (Y (i+1)) (Y i) (α i) (ρ i) := by
    induction hN using Nat.decreasingInduction with
    | self =>
      obtain ⟨R,H⟩ := hp N
      refine ⟨fun _=> R,0,fun _ _ _ _=>0,H,fun i hi hu=> ?_,by intros; omega⟩
      rw [le_antisymm hu hi]; exact H.1
    | of_succ i hi I =>
      obtain ⟨Y,α,ρ,hY,he,H⟩ := I
      obtain ⟨E,w,θ,hD⟩ := hr.pays i N hi _ (he (i+1) le_rfl hi)
      refine ⟨update Y i (sat D V N i E),update α i w,update ρ i θ,?_,?_,?_⟩
      · rw [update_of_ne hi.ne']; exact hY
      · intro m hm hv; rcases eq_or_lt_of_le hm with heq|heq
        · subst m; rw [update_self]; exact hD.bubble.lives
        rw [update_of_ne heq.ne']; exact he m (Nat.succ_le_of_lt heq) hv
      intro m hv hx; rcases eq_or_lt_of_le hv with heq|heq
      · subst m; rw [update_self,update_self,update_self,update_of_ne (by omega)]; exact ⟨_,rfl,hD⟩
      rw [update_of_ne (by omega : m+1 ≠ i),update_of_ne (by omega : m≠i),update_of_ne (by omega : m ≠ i),update_of_ne (by omega : m≠i)]; exact H m heq hx
  choose Y α ρ H H' hq using fun N=> he N 0 (Nat.zero_le _)
  let V0 : Kin V Z := ⟨α,Y,ρ⟩; refine ⟨V0,?_,fun N m h=> hq N m (by omega) h⟩
  have HI N m (hm: 0≤m)(hi:m<N): Bubble V Q Z N m (Y N (m+1)) (Y N m) (α N m) (ρ N m):=by
    obtain ⟨x,hx,hT⟩:= hq N m hm hi; rw [← hx]; exact hT.bubble
  refine ⟨?_,fun N m h=> (H' N m (by omega) h).row,fun N m p F hm=> (HI N m (by omega) hm|>.steps p F).2.2.2.2⟩
  refine ⟨h.stage.symm,h.lengths.symm,fun N m hm=> (H' N m (by omega) hm).ties,fun N m hm => (H' N m (by omega) hm).bound,
    fun N i=>(H N).2.1 i,fun N i=> (H N).2.2 i,fun N m p hm F=>(HI N m (by omega) hm|>.steps p F).1,
    fun N m p hm F=>?_,fun N m p hm F=> (HI N m (by omega) hm|>.steps p F).2.2.2.1,fun N m hm=> (HI N m (by omega) hm).earns,fun N m p hm F=> ?_⟩
  · exact ⟨(HI N m (by omega) hm|>.steps p F).2.1,(HI N m (by omega) hm|>.steps p F).2.2.1⟩
  exact higher_bill ((HI N m (by omega) hm|>.steps p F).2.2.2.2) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hl _) (Q.pos _).le) (Real.exp_pos _).le)

def Coins (V:Horizon a)(D:Knobs a)(Q:PostCost L)(Z:ChartRatio G)(ε:ℝ)(x:ℕ→ Cube G)(α: ℕ→ℝ):= ∀ i,x i ∈ (label D i).valid ∧ ‖x i‖≤ε ∧ EdgeLaw V D Q Z ε i (x (i+1)) (x i) (α i)
lemma ties {x y:ℕ→ Cube G}{α β}(p:G.ColorIndex)(hz:LocalRatio Z)(hp:Ahead wavePulse ε)(h:Mints D P V Q Z ε)(hr:Buried V)(hx:Coins V D Q Z ε x α)(hy:Coins V D Q Z ε y β):x=y∧α=β:=by
  let d i:= ‖y i-x i‖
  have hd i: d i≤2*ε:= (norm_sub_le ..).trans (by linarith [(hx i).2.1,(hy i).2.1])
  have hu i : d i≤ (1/2:ℝ)* d (i+1):=step_contracted p hz hp h hr (hx _).1 (hy _).1 (hx _).2.1 (hy _).2.1 (hx _).2.2 (hy _).2.2
  have he: x=y:=by
    funext i
    have he (n:ℕ) : ∀ i,d i ≤ (1/2:ℝ)^n*(2*ε):= by
      induction n with
      | zero=> simpa using hd
      | succ n ih=>
        intro i; rw [pow_succ',mul_assoc]; exact le_trans (hu i) (mul_le_mul_of_nonneg_left (ih _) (by positivity))
    have hv:d i ≤ 0:= ge_of_tendsto (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0≤(1/2:ℝ) by norm_num) (by norm_num)).mul_const (2*ε)) (Eventually.of_forall fun n=> he n i)
    exact (sub_eq_zero.mp (norm_le_zero_iff.mp hv)).symm
  refine ⟨he,funext (fun i=> (common (y:=y i) p hz hr (h.work i) ?_ ((hy i).2.2)).2)⟩; rw [← he]; exact (hx i).2.2

lemma earned {T:Kin V Z}{Y:ℕ→ℕ→Cube G} (hp:∀ n i,i<n→ Courtesy V D Q Z ε n i (T.path n (i+1)) (Y n i) (T.alpha n i) (T.stationary n i)) (he:∀ n i,i<n→ sat D V n i (Y n i)=T.path n i)
    (_h:Mints D P V Q Z ε)(t:ℕ→ℕ)(ht:StrictMono t):∃ u:ℕ→ℕ,StrictMono u∧ ∃ x α,Coins V D Q Z ε x α∧∀ i,HLimit (fun n=> Y (t (u n)) i) (x i)∧ Tendsto (fun n=> T.alpha (t (u n)) i) atTop (𝓝 (α i)):=by
  let E i:= (a.params (i+1)).drift+ |G.slopeConstant*Real.log (a.S.block i).val|
  have hb i n (hh:i<n):T.alpha n i ∈ Metric.closedBall 0 (E i):=by
    rw [Metric.mem_closedBall,dist_zero_right]; exact driving_abs _ _ _ ((hp _ _ hh).bubble.earns)
  let F i j:= T.alpha (t j) i
  obtain ⟨s,α,hs⟩:= Extraction.simultaneous F (K:=fun i=> Metric.closedBall 0 (E i)) (fun _=> isCompact_closedBall ..) (fun i=> (ht.tendsto_atTop.eventually (eventually_gt_atTop i)).mono fun j h=> hb _ _ h)
  let I:=Crates G; have hg i n (h:i<n): ‖Y n i‖≤ε:= (hp n i h).toll
  let U (b : ℕ × I) j:= (Y (t (s j)) b.1) b.2
  have hv:=ht.tendsto_atTop.comp s.cofinal
  obtain ⟨u,k,hk⟩:= Extraction.simultaneous U (K:=fun _=> Metric.closedBall 0 ε) (fun _=> isCompact_closedBall ..) (fun i=> by
    filter_upwards [hv.eventually_gt_atTop i.1] with j hj; rw [Metric.mem_closedBall,dist_zero_right]; exact (lp.norm_apply_le_norm (by norm_num) _ _).trans (hg _ _ hj))
  let v:= t ∘ s.choose ∘ u.choose
  have hr:Tendsto v atTop atTop := hv.comp u.cofinal
  have hB i: ∀ᶠ n in atTop, ‖Y (v n) i‖≤ε:= (hr.eventually_gt_atTop i).mono (fun n h=>hg i _ h)
  have hw i:∃ x,HLimit (fun n=> Y (v n) i) x:=by
    let z j:= k (i,j)
    let f n:= Y (v n) i
    have he : Tendsto (fun n=> ⇑(f n)) atTop (𝓝 z):= tendsto_pi_nhds.mpr (fun j=> (hk (i,j)).2)
    have hx:Bornology.IsBounded (Set.range f):=by
      obtain ⟨l,hL⟩:= eventually_atTop.1 (hB i)
      let Z := f '' Set.Iio l
      apply ((Set.finite_Iio l).image f |>.isBounded |>.union (Metric.isBounded_closedBall (x:=0) (r:=ε))).subset
      refine Set.range_subset_iff.mpr (fun n=> ?_); cases lt_or_ge n l with
      | inl h=> exact Set.mem_union_left _ ⟨n,h,rfl⟩
      | inr h=> exact Set.mem_union_right _ (Metric.mem_closedBall.mpr ((dist_zero_right _).trans_le (hL _ h)))
    exact ⟨(⟨(z: PreLp (fun _ : I=>ℝ)),lp.memℓp_of_tendsto (F:=f) hx he⟩:Cube G), ⟨ε,hB _⟩,tendsto_pi_nhds.mp he⟩
  choose x hQ using hw
  have hL i:Tendsto (fun n=> T.alpha (v n) i) atTop (𝓝 (α i)):= (hs _|>.2).comp u.cofinal
  refine ⟨s.choose∘u.choose,s.monotone.comp u.monotone,x,α,?_,fun i=>⟨hQ i,hL _⟩⟩
  intro i
  have hx: (label D i).Inked (x i) := (label D i).areas.2 _ (hQ i) ((hr.eventually_gt_atTop i).mono (fun n hi=> (hp _ _ hi).above.2))
  refine ⟨hx,(hQ _).norm_le (hB _),?_⟩
  obtain ⟨l,hq⟩:= eventually_atTop.1 (hr.eventually_gt_atTop (i+1)); let r:= fun n=> l+n
  have hW:Tendsto r atTop atTop:= tendsto_atTop_mono (fun j=> (show j≤r j by unfold r; omega)) tendsto_id
  refine ⟨v∘r,hr.comp hW,fun n=>Y (v (r n)) (i+1),fun n=>Y (v (r n)) i,fun n=> T.alpha (v (r n)) i,fun n=> T.stationary (v (r n)) i,fun n=> ?_,(hQ _).upon hW,(hQ _).upon hW,(hL i).comp hW⟩
  have hi : i+1 < v (r n):=hq _ (by unfold r; omega)
  exact ⟨by change i < v _; omega,(hp _ _ hi).bubble.lives,by simp only [Function.comp_apply]; rw [he _ _ hi]; exact hp _ _ (by omega)⟩

lemma turning (hP : Paid w a) (p:G.ColorIndex)(hz:LocalRatio Z)(hp:Ahead wavePulse ε)(h:Mints D P V Q Z ε)(hr:Buried V): ∃ T:Kin V Z, FullPaths T Q ∧ ∃ Y : ℕ→ℕ→ Cube G, (∀ n i,i<n→ Courtesy V D Q Z ε n i (T.path n (i+1)) (Y n i) (T.alpha n i) (T.stationary n i)) ∧
    (∀ n i,i<n→ sat D V n i (Y n i)= T.path n i) ∧ ∃ x α,Coins V D Q Z ε x α∧ ∀ i,HLimit (fun n=> Y n i) (x i) ∧ Tendsto (fun n=> T.alpha n i) atTop (𝓝 (α i)):=by
  obtain ⟨T,hT,H⟩:=fieldArray hP h.pulse h.blanket h
  have hx n i: ∃ x, i<n→ sat D V n i x=T.path n i∧ Courtesy V D Q Z ε n i (T.path n (i+1)) x (T.alpha n i) (T.stationary n i):=by
    by_cases hi:i<n
    · obtain ⟨x,h,c⟩:= H n i hi; exact ⟨x,fun _=>⟨h,c⟩⟩
    exact ⟨0,fun hh=>False.elim (hi hh)⟩
  choose x hx using hx
  have hP n i hi:=(hx n i hi).2
  have hQ:=earned hP (fun n i hi=> (hx n i hi).1) h
  obtain ⟨_,_,U,A,hA,-⟩:= hQ id strictMono_id
  refine ⟨T,hT,x,hP,(fun n i hi=> (hx n i hi).1),U,A,hA,fun i=>⟨⟨⟨ε,(eventually_gt_atTop i).mono fun n hn=> (hx n i hn).2.toll⟩,fun j=> subseq_rule fun f hf=> ?_⟩,subseq_rule fun f hf=>?_⟩⟩
  · obtain ⟨g,hg,y,α,h1,h2⟩:= hQ f hf; rw [← (ties p hz hp h hr hA h1).1] at h2; exact ⟨g,hg,(h2 i).1.hit j⟩
  obtain ⟨g,hg,y,α,h1,h2⟩:= hQ f hf; rw [← (ties p hz hp h hr hA h1).2] at h2; exact ⟨g,hg,(h2 i).2⟩
end YM.UVExtension.Reward
