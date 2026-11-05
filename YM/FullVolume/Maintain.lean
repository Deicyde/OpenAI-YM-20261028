import YM.FullVolume.Windows

/-!
# Unextracted probing

Unlike the period-and-volume argument in Purchases, rank used here
cannot wait for any extraction. Don't lose uniformity in p near the
projection boundaries: these particular real probes fit everywhere.
Venues are epsilon-near free tests at a fixed stopping level.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Set Filter Metric MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Next.Rank Next.Rank.Market Push.RelayDifference
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}{C:Family G}{S:Table C.book}{d : ℕ}{X:Columns C S d} (T:X.Trials) (hm:C.Makes)(hp: Wcmain C) (h:Purchases T)
    (k:ℕ)(l:List Axis)

def boostsAt (c:Fin (X.dim+1))(i:Cutoffs) : C.label d:= T.lift k i.1 i.2 c

def focus (j : Fin X.amount) (c : Fin (X.dim+1)) := (X.row j).tests (standard C) X.basis (X.basis c)

include h hm
lemma gaugesFull (ε:ℝ) (hε:0<ε) :
    ∀ᶠ k:ℕ in atTop, ∀ᶠ i in mesh, ∀ (j : Fin X.amount) (c : Fin (X.dim+1)),
      dist (monitor (siblings T k j) i (Bid.upper C (boostsAt T k c)) (loc T k j i)) (focus (X:=X) j c) < ε:=by
  classical
  let p k i (j:Fin X.amount) (c: Fin (X.dim+1)):= monitor (siblings T k j) i (Bid.upper C (boostsAt T k c)) (loc T k j i)
  let T':= standard C
  have he (j : Fin X.amount) (c:Fin (X.dim+1)): ∀ᶠ k:ℕ in atTop,∀ᶠ i in mesh, dist (p k i j c) (focus (X:=X) j c) < ε:=by
    have hi:= (T'.class_smooth T' (Maxwell.table_smooth _) (roles X j c)).continuousOn
    let x := (X.row j).expected; let F k:= T'.useAt T' (T.tested k j) (roles X j c); have hx:= generic_conf _ (X.row j|>.probes)
    have hL : Tendsto F atTop (𝓝 (focus (X:=X) j c)):= by rw [focus,← roles_score]; exact ((hi _ hx).continuousAt ((conf_open _).mem_nhds hx)).tendsto.comp (h.tuned j)
    filter_upwards [(h.monitor_tends j c).eventually (gt_mem_nhds (half_pos hε)),Metric.tendsto_nhds.mp hL (ε/2) (half_pos hε)] with k hk hv
    filter_upwards [deepen.eventually (h.arrays k)] with i hi
    obtain ⟨hK,H⟩:=hi
    have hX:= Read.full_cost (N:=i.1) (u:=T.mark k j) (t:=pulse T k i.1 i.2 j c) hm (freed (h.axis k j)) (T.allowed k) (Cells.center C.S i.2 ((T.window k).trans hK) 0) ((H i.2 j c).1) ((H i.2 j c).2)
    have hb: p k i j c=C.numeric i.1 i.2 (pulse T k i.1 i.2 j c) (fun u=> location C.S (T.depth k) i.1 i.2 (T.mark k j u)) := by
      unfold p; rw [ridge]; unfold lifted
      congr 1
      · funext u; refine Fin.cases ?_ (fun u=> ?_) u <;> rfl
      funext u; exact loc_wrap T k j i hK u
    apply lt_of_le_of_lt (dist_triangle _ (F k) _)
    have ha : dist (p k i j c) (F k) < ε/2:= by rw [hb,dist_eq_norm]; exact hX.trans_lt hk
    linarith only [ha,hv]
  filter_upwards [eventually_all.mpr (fun j => eventually_all.mpr (he j))] with k hk using eventually_all.mpr (fun j=> eventually_all.mpr (hk j))

omit h
structure VitalRank : Prop where
    shops : Booths T
    performance (ε:ℝ)(hε:0<ε): ∀ᶠ k:ℕ in atTop, ∀ᶠ i in mesh, ∀ (j : Fin X.amount) (c : Fin (X.dim+1)),
      dist (monitor (siblings T k j) i (Bid.upper C (boostsAt T k c)) (loc T k j i)) (focus (X:=X) j c) < ε
include h in
lemma took : VitalRank T:= ⟨invested T h,gaugesFull T hm h⟩
variable (h':Booths T)
include hp h'
lemma probesUp {ε:ℝ}(hε:0<ε)(k:ℕ):
    ∀ᶠ b:ℝ in 𝓝[>] 0, ∀ᶠ i in mesh, ∀ (j : Fin X.amount) (c:Fin (X.dim+1)),
        dist (probe T k i b l (boostsAt T k c i) j) (monitor (siblings T k j) i (Bid.upper C (boostsAt T k c)) (loc T k j i)) ≤ ε := by
  obtain ⟨A,hA⟩:= h'.bounded k
  let p (j: Fin X.amount)(i:Cutoffs)(c:Fin (X.dim+1)):= monitor (siblings T k j) i (Bid.upper C (boostsAt T k c))
  have hQ(j:Fin X.amount): ∀ᶠ b:ℝ in 𝓝[>] 0, ∀ᶠ i in mesh, ∀ c:Fin (X.dim+1), dist (probe T k i b l (boostsAt T k c i) j) (p j i c (loc T k j i)) ≤ ε:=by
    obtain ⟨t,ht,hS⟩:= lobby T h' hm hp k j A ε hε
    have hy: ∀ᶠ b:ℝ in 𝓝 0, l.length*(2*b) ≤ t:= (show Continuous (fun b:ℝ=> l.length*(2*b)) by fun_prop).continuousAt.eventually (ge_mem_nhds (by simpa using ht))
    filter_upwards [self_mem_nhdsWithin, hy.filter_mono (nhdsWithin_le_nhds)] with b (hb : b∈Ioi 0) hB
    filter_upwards [hS,deepen.eventually_ge_atTop (T.depth k),deepen.eventually (step_upper C.S hb)] with i hi hh hL c
    let a:= C.S.a i.1
    rw [probe_eq _ _ _ _ _ (boostsAt T k c)]
    apply closer a (steps C.S b i.1) l hL.1 (C.S.a_pos _) (T.realPlace k j) (show a*steps C.S b i.1 ≤2*b from (mul_comm ..).trans_le hL.2.2) (p j i c)
      (loc T k j i) (R:=t)
    · intro y he
      let v:= Fin.cons (α:=fun _ : Fin ((X.row j).extra+1)=> C.label d) (boostsAt T k c i) (fun u=> wisps T k j u i)
      unfold p; rw [ridge,ridge]; apply le_of_lt (hi v (fun u=> ?_) y he)
      refine Fin.cases ?_ (fun j' => ?_) u
      · exact hA _ _ _
      exact hA _ _ _
    rw [loc_tag T k j i hh, dist_self]; linarith
  filter_upwards [eventually_all.mpr hQ] with b hb using eventually_all.mpr hb

lemma siblingsPrice (k : ℕ) (j) : ∃ v:(Fin (X.row j).extra)→ℕ→ℝ, ∀ u, Affords (siblings T k j u) (fun k _=> v u k):=by
  obtain ⟨Z,h⟩:= h'.bounded k
  choose v hv using fun u => Funded.primaries hm hp (wisps T k j u) (Y:=Z) (Eventually.of_forall fun i=> h i.1 i.2 _)
  exact ⟨v,hv⟩

/-- detector action at one offset. -/
lemma warded (k:ℕ)(j):∃ t:ℝ,0<t∧ ∀ (F:Trial C) (u:ℕ→Cutoffs→ℝ), Affords F u →
    ∀ᶠ w:ℕ in atTop, ∃ A:ℝ,0≤A ∧ ∀ᶠ i in mesh,∀ x,
        dist (tag (C.S.a i.1) x) (T.realPlace k j) ≤ t → ‖monitor (siblings T k j) i F x‖ ≤ u w i*A := by
  obtain ⟨t,r,ht,hr,hK⟩:= arena T h' k j; let g:=4*r
  have hg : 0<g:=by unfold g; positivity
  obtain ⟨v,hV⟩:= siblingsPrice T hm hp h' k j
  let H w k:= max 1 (v w k)
  refine ⟨t,ht,fun F u hF =>?_⟩
  let E:= Fin.cons (α:=fun _ : Fin ((X.row j).extra+1)=> ℕ→ Cutoffs→ℝ) u (fun i k _=> H i k)
  have he i:Affords ((Fin.cons (α:=fun _ : Fin ((X.row j).extra+1)=>Trial C) F (siblings T k j)) i) (E i):=by
    refine Fin.cases hF (fun r=> ?_) i; exact (hV r).enlarged (Eventually.of_forall (fun i=> Eventually.of_forall (fun j=> le_max_right ..)))
  filter_upwards [cohort hm (Fin.cons F (siblings T k j)) he hg] with w hw
  refine ⟨∏ z,H z w,Finset.prod_nonneg (fun _ _=>zero_le_one.trans (le_max_left ..)),?_⟩
  filter_upwards [hw] with i hi x hX; refine le_trans (hi (wrap _ ∘ x) (fun u v huv=>?_)) ?_
  · exact gridSeparation C.S _ rfl (fun l l' he=> ⟨0,hK _ hX i.2 l l' he (0:Axis)⟩) v u huv.symm
  rw [Fin.prod_univ_succ]; simp [E]

/-- Average detector on a difference with an already-funded primary. -/
lemma invites (k:ℕ): ∀ᶠ b:ℝ in 𝓝[>] 0,
    (∀ (F:Trial C), Funded F → (∀ N p x,Continuous (F N p x)) → ∃ v:ℝ,∀ᶠ i in mesh, ‖assay T k i b l (hops F l)‖ ≤ v) ∧
      ∀ (F:Trial C) (u:Cutoffs→ℝ), Owed F u → Tendsto u mesh (𝓝 0) → Tendsto (fun i=> assay T k i b l F) mesh (𝓝 0):=by
  classical
  choose t ht hT using warded T hm hp h' k
  have he j: ∀ᶠ b:ℝ in 𝓝 0, l.length*(2*b) ≤ t j:=
    (show Continuous (fun b:ℝ=> l.length*(2*b)) by fun_prop).continuousAt.eventually (ge_mem_nhds (by simpa using ht j))
  filter_upwards [self_mem_nhdsWithin,(eventually_all.mpr he).filter_mono nhdsWithin_le_nhds] with b (hb : b∈Ioi 0) hB
  have hv:0<b:=hb
  constructor
  · rintro F ⟨u,hu⟩ hL
    let g:= hops F l
    have hW(j:Fin X.amount):∃ A:ℝ, 0≤A∧ ∀ᶠ i in mesh, ‖assay T k i b l g j‖ ≤ A:=by
      obtain ⟨w,A,ha,h⟩:= (hT j F _ hu).exists
      let a:=(max 0 (u w))*A
      have hx:0≤a:=mul_nonneg (le_max_left ..) ha
      let Z:= (2/b)^l.length*a
      refine ⟨Z,mul_nonneg (by positivity) hx,?_⟩
      filter_upwards [h,deepen.eventually_ge_atTop (T.depth k),deepen.eventually (step_upper C.S hb)] with i hi hd hj
      unfold assay g; rw [scores_hops _ _ _ hL (fun j x=> C.continuousO ..)]
      have hz:=reserve_abs (C.S.a i.1) (steps C.S b i.1) l hj.1 (C.S.a_pos i.1) (T.realPlace k j) hb hj.2.1 hj.2.2 _ hx (fun x (h':_ ≤ t j)=> le_trans (hi x h') (mul_le_mul_of_nonneg_right (le_max_right _ (u w)) ha)) (loc T k j i) ?_
      · exact hz
      rw [loc_tag T _ _ _ hd,dist_self]; linarith [hB j]
    choose v H hP using hW
    obtain ⟨u,hv,hQ⟩:= ((eventually_ge_atTop (0:ℝ)).and (eventually_all.mpr (fun j=> eventually_ge_atTop (v j)))).exists
    refine ⟨u,?_⟩; filter_upwards [eventually_all.mpr hP] with i hi; exact (pi_norm_le_iff_of_nonneg hv).mpr (fun j=> (hi j).trans (hQ j))
  intro F u hF hL
  apply tendsto_pi_nhds.mpr
  intro j
  obtain ⟨w,A,hA,h⟩:= (hT j F _ hF).exists
  rw [tendsto_iff_norm_sub_tendsto_zero]; simp only [Pi.zero_apply,sub_zero]
  have hp:= hL.mul_const A; rw [zero_mul] at hp
  refine squeeze_zero' (Eventually.of_forall (fun i=> norm_nonneg _)) ?_ hp
  filter_upwards [h,deepen.eventually_ge_atTop (T.depth k),deepen.eventually (step_upper C.S hb)] with i hi hv ht
  apply rounds _ _ l ht.1 (C.S.a_pos _) (T.realPlace k j) (show C.S.a i.1*steps C.S b i.1 ≤ 2*b from (mul_comm ..).trans_le ht.2.2) _ (hi) _
  rw [loc_tag T _ _ _ hv,dist_self]; linarith [hB j]
end YM.FullVolume
