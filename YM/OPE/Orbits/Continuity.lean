import YM.OPE.Orbits.Separated

/-! Measurability/local smoothness inputs for joint coefficient testing.
Separate continuity in character (weak theorem on fixed separated
configurations) and location suffices here. Do not require a jointly smooth
representative in phase and positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Set Filter MeasureTheory Table Extraction TopologicalSpace
open scoped Topology BigOperators ContDiff Classical ENNReal Matrix.Norms.Frobenius
section Borel
variable {X Y:Type*}[MeasurableSpace X] [MetricSpace Y] [SeparableSpace Y] [MeasurableSpace Y][BorelSpace Y][Nonempty Y]

private def scale (m:ℕ):ℝ:=1/(m+1)
lemma seq_hit (m:ℕ)(y:Y) : ∃ j:ℕ,dist y (denseSeq Y j) < scale m := Metric.denseRange_iff.mp (denseRange_denseSeq Y) y (scale m) (by dsimp only [scale]; positivity)
private def hit (m:ℕ)(y:Y):ℕ:= Nat.find (seq_hit m y)
private lemma hit_meas (m:ℕ): Measurable (fun y:Y=>hit m y):=by
     apply measurable_find; intro z; apply Continuous.measurable (f:=fun q=>dist q (denseSeq Y z)) ?_ isOpen_Iio.measurableSet; fun_prop
private lemma approximates (y:Y): Tendsto (fun m=>denseSeq Y (hit m y)) atTop (𝓝 y):= Metric.tendsto_nhds.mpr fun ε hε=>
     (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually (gt_mem_nhds hε) |>.mono fun m hm => by
       have hi:= Nat.find_spec (seq_hit m y); rw [dist_comm]; exact (hi.trans (hm:scale m < ε))

lemma measurable_mixed (f:Y→X→ℂ)(hf:∀ x,Continuous (fun y=>f y x))(hs:∀ y,Measurable (f y)): Measurable (fun z:X×Y=>f z.2 z.1) :=by
    classical
    let g m(z:X×Y):=f (denseSeq Y (hit m z.2)) z.1
    have hL:Tendsto g atTop (𝓝 (fun z:X×Y=>f z.2 z.1)):= by apply tendsto_pi_nhds.mpr; intro x; exact ((hf x.1).continuousAt.tendsto.comp (approximates x.2))
    refine measurable_of_tendsto_metrizable (fun m=> ?_) hL
    intro z hz
    have he:(g m ⁻¹' z)= ⋃ i:ℕ, ((f (denseSeq Y i) ∘ Prod.fst) ⁻¹' z) ∩ (hit m ∘ Prod.snd) ⁻¹' {i}:=by ext q; simp [g, Function.comp_apply]
    rw [he]; refine MeasurableSet.iUnion fun i=> ((hs _|>.comp measurable_fst) hz).inter ((hit_meas m|>.comp measurable_snd) (measurableSet_singleton _))
end Borel

variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book} (U:Spec.Final C F S)
    (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    {I J:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ}(v:Labels S d)(w:Labels S e)(m:ℕ)
abbrev Loc (I J:Type) := (I→E4)× E4 ×(J→E4)
def guardZone (m:ℕ):Set (Loc I J):={z| (∀ n:ℕ,n ≤ m→ orbitMargin R.port n z.1 z.2.1) ∧ Injective (beside z.1 z.2.2) ∧ Injective (beside (sole z.2.1) z.2.2)}
-- binders include U R explicitly? notation
lemma guard_open : IsOpen (guardZone (I:=I) (J:=J) U R m):=by
    unfold guardZone; apply isOpen_iff_mem_nhds.mpr; intro z hz
    have h0(n) (h:n≤ m):∀ᶠ t:Loc I J in 𝓝 z,orbitMargin R.port n t.1 t.2.1:=
         (continuous_fst.prodMk continuous_snd.fst).continuousAt.tendsto.eventually (p:=fun x:(I→ E4) ×E4 => orbitMargin R.port n x.1 x.2) ((margin_open n).mem_nhds (hz.1 n h))
    have h1:∀ᶠ t:Loc I J in 𝓝 z,∀ n:Fin (m+1),orbitMargin R.port n.val t.1 t.2.1:= eventually_all.mpr (fun n=>h0 _ (Nat.le_of_lt_succ n.isLt))
    have hG:Continuous (fun z:Loc I J=> beside z.1 z.2.2):= by apply continuous_pi; rintro (i|j); exact (continuous_apply (A:=fun _:I=>E4) i).comp continuous_fst; exact (continuous_apply (A:=fun _:J=>E4) j).comp continuous_snd.snd
    have hG':Continuous (fun z:Loc I J=> beside (sole z.2.1) z.2.2):=by apply continuous_pi; rintro (i|j); exact continuous_fst.comp continuous_snd; exact (continuous_apply (A:=fun _:J=>E4) j).comp continuous_snd.snd
    filter_upwards [h1,(hG.continuousAt.tendsto.eventually (p:=fun q=>Injective q) (open_inj.mem_nhds hz.2.1)),(hG'.continuousAt.tendsto.eventually (p:=fun q=>Injective q) (open_inj.mem_nhds hz.2.2))] with i h₁ h₂ h₃ using ⟨fun n hn=>h₁ ⟨_,Nat.lt_succ_of_le hn⟩,h₂,h₃⟩

def armed (m:ℕ):Set (Loc I J):=guardZone U R m
lemma whole_cont_at (T:Table C.book) (hT:T.Hierarchy) {x:Loc I J}(h:Injective (beside x.1 x.2.2)):
    ContinuousAt (fun z:Loc I J=> whole T z.1 v z.2.2 w) x :=by
       simp_rw [whole_observed]; apply ContinuousAt.comp ?_ (show Continuous _ from ?_).continuousAt (g:=fun x=> observe T x (beside (names v) (names w)))
       · exact smooth_observe T hT.smooth (x:=beside x.1 x.2.2) _ h
       apply continuous_pi; rintro (i|j); exact (continuous_apply (A:=fun _:I=>E4) i).comp continuous_fst; exact (continuous_apply (A:=fun _:J=>E4) j).comp continuous_snd.snd
lemma alone_cont_at (T:Table C.book) (hT:T.Hierarchy){x:Loc I J}(m:ℕ)(u:S.Field m)(hy:Injective (beside (sole x.2.1) x.2.2)) : ContinuousAt (fun z:Loc I J=>upon T m z.2.1 z.2.2 w u) x:=by
    change ContinuousAt ((fun t:Loc Unit J=>whole T t.1 (d:=fun _:Unit=>m) (sole u) t.2.2 w) ∘ (fun t:Loc I J=>(sole t.2.1,t.2.1,t.2.2))) _; apply ContinuousAt.comp (whole_cont_at ..) (Continuous.continuousAt (by unfold sole; try fun_prop))
    all_goals assumption

private lemma cont_sum {Y:Type*}[TopologicalSpace Y]{i:Type*}(s:Finset i) (f:i→Y→ℂ){x:Y}(h:∀ j∈s,ContinuousAt (f j) x):ContinuousAt (fun z=>∑ j∈ s,f j z) x:=by
    induction s using Finset.cons_induction with
    | empty=>simp only [Finset.sum_empty]; exact continuousAt_const
    | cons j s hj ih=> simp only [Finset.sum_cons]; exact (h j (by simp)).add (ih (fun i hi=>h i (by simp [hi])))
lemma trunc_cont_at (r:Viewers U){z:Loc I J}(h:z∈guardZone U R m): ContinuousAt (fun t:Loc I J=> OPE.Orbits.trunc (spectator U r) U R m t.1 t.2.1 v t.2.2 w) z:=by
    unfold Orbits.trunc; refine cont_sum _ (fun j:Fin (m+1)=> _) ?_
    intro j hj; apply cont_sum; intro i hi
    let f (t:Loc I J):= R.coef j.val i t.1 v t.2.1
    let T:=spectator U r
    exact ContinuousAt.mul (f:=f) (g:=fun t:Loc I J=> upon T _ t.2.1 t.2.2 w (R.actor j.val i)) (ContinuousAt.comp (f:=(fun t:Loc I J=> (t.1,t.2.1))) (R.coef_smooth j.val _ (h.1 j.val (Nat.le_of_lt_succ j.isLt)) v).continuousAt (by fun_prop)) (alone_cont_at w T (spectate U r) _ _ h.2.2)

private lemma phase_cont_word {z:Loc I J}(he:Injective (beside z.1 z.2.2)):
    Continuous (fun i:U.α.space.X=> whole (U.α.ensemble i) z.1 v z.2.2 w) := by
      have h':= U.phase.phase.decomposition
      have h:=U.phase.phase.decomposition.weak (viewing U (beside z.1 z.2.2) (beside (names v) (names w))); exact h.congr (fun i=> (character_sees U i _ _ he).trans ((whole_observed ..).symm))

lemma indicator_meas (v':Viewers U): Measurable (fun z:Loc I J=>(guardZone U R m).indicator (fun t:Loc I J=>formula U R t.1 t.2.1 v t.2.2 w m v') z):=by
   apply (show ContinuousOn (fun t:Loc I J=>formula U R t.1 t.2.1 v t.2.2 w m v') (guardZone U R m) from fun z hz=> ContinuousAt.continuousWithinAt (ContinuousAt.sub (f:=fun t:Loc I J=>whole (spectator U v') t.1 v t.2.2 w) (whole_cont_at v w _ (spectate U v') hz.2.1) (trunc_cont_at ..))).measurable_piecewise continuousOn_const (guard_open U R m|>.measurableSet)
   all_goals tauto
lemma mixed_meas : Measurable (fun z:Loc I J × U.α.space.X=> (guardZone U R m).indicator (fun q:Loc I J=>formula U R q.1 q.2.1 v q.2.2 w m (some z.2)) z.1):=by
   letI : Nonempty U.α.space.X:=⟨U.α.atPoint⟩
   refine measurable_mixed _ (fun x=>?_) (fun y=>indicator_meas U R v w m (some y))
   by_cases hx:x∈ guardZone (I:=I) (J:=J) U R m
   · simp only [Set.indicator_of_mem hx]; unfold formula Orbits.trunc
     change Continuous ((fun i=>whole (U.α.ensemble i) x.1 v x.2.2 w) - (fun i:U.α.space.X=>∑ j:Fin (m+1),∑ t:R.channels j.val, _*whole (U.α.ensemble i) _ _ _ _))
     refine Continuous.sub (phase_cont_word (z:=x) _ _ _ hx.2.1) (continuous_finsetSum _ fun j hj=> continuous_finsetSum _ fun t ht=> Continuous.mul (f:=fun _:U.α.space.X=> R.coef j.val t x.1 v x.2.1) continuous_const ?_)
     apply phase_cont_word (z:=((sole x.2.1,x.2.1,x.2.2):Loc Unit J)) U (sole (R.actor j.val t)) w hx.2.2
   simp only [Set.indicator_of_notMem hx]; exact continuous_const
end YM.OPE.Orbits
