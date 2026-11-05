import YM.TraceExtension.Verse.Pears
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Verse
open Function Filter Set Extraction Cells OS OS.Ground Lattice Spec MeasureTheory Wilson
open RG Terrace MergeProof.East Next.Rank Next.Rank.East Next.UVStress Further.CorrectedLift Climb
open Glyph Next.Rank.Station Next.Rank.Tapes.West Analysis Marker Edition
open scoped Topology BigOperators InnerProductSpace Classical ContDiff
variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} {V:Chamber S timeAxis}{A:Spread V}{p:A.Resolution}{k b i n d: ℕ}
variable {H:(Cells.standard C).Hierarchy}{J:Scaling S}{W:∀ i,Vane C i}{Y:∀ d _:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}(hq:Gondola f H J 𝓛 W Y)
local notation "S'"=> Cells.standard C
local notation "A'"=> C.path.levels
local notation "U'"=> (𝓛:Filter (ℕ×ℕ))

include hq
lemma rounds (h:G.Simple)(x:Points n) : Tendsto (fun i => fad (W i) x) atTop (𝓝 x):=by
    let u(i):=mag (A') (W i).b (W i).k
    have he:= (mag_rate (A') h (by norm_num:(0:ℝ)<5)).comp hq.growth
    have hu:Tendsto u atTop atTop:= tendsto_atTop_mono (fun i=> Real.rpow_le_rpow_of_exponent_le (show 1 ≤ (A').clock.monitor (W i|>.k) from Real.one_le_exp (sq_nonneg _)) (hq.season i|>.1.high.1.le)) he
    have hp:= tendsto_inv_atTop_zero.comp hu
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (fun _=> dist_nonneg) (fun i => Eq.trans_le (congr_arg (fun y=> dist y x) (Next.Rank.Station.reading (A') (W i).b (W i).k x)) (Extraction.approximate (inv_pos.mpr (mag_pos ..)) x)) ?_
    simpa only [mul_zero] using! hp.const_mul (4*n:ℝ)
lemma mixed (x:Points 2)(i:ℕ)(hh:fad (W i) x ∈ generic 2) (ht:‖fad (W i) x‖ ≤ 100):FitSky (A') (W i).b (W i).k x:=by
    let U:= W i;let a:=mag (A') U.b U.k; let y:= fad U x; let t:= Verse.flat U x
    have he:y=tag a⁻¹ t:= Next.Rank.Station.reading _ _ _ _
    have hx : Next.Rank.Station.choose (A') U.b U.k y=t:=by rw[he]; exact (authentic (V:=A') t).1
    have hv :FitSky (A') U.b U.k y:=by
       rw [he]; exact (hq.season i).1.plate.width t (he ▸ hh) (he ▸ ht)
    have hw : Next.Rank.Station.key (A') U.b U.k y=rum U x:=by unfold Next.Rank.Station.key; rw [hx];rfl
    exact ⟨show rum U x∈generic _ from hw ▸ hv.usable,fun i j=> show |rum U x i j|≤ _ from hw ▸ hv.deep i j⟩
variable (w:Seed C f S)(hf:(𝓛:Filter _) ≤ f.fuse) (R:p.Out)(hv:Steady V){K:p.X→Table C.book}(hs:∀ i,(K i).Hierarchy)(hy:∀ i,p.receives (K i) i)
    (x':p.X)(hr:(K x').respects S)(h:G.Simple){x:Points 2}(hh:x∈generic 2)(ht:Scaling.window 100 2 ∈ 𝓝 x)
include w hf R hv hs hy hr h hh ht
lemma greens (t:Fin 2→PegC C d):
    let T:= fun j:Fin 2=> PoleC C d (t j)
    Tendsto (fun i=> S.classMoment (K x') (fun _=>d) (rum (W i) x) (fun j=> J.U i d (T j))) atTop (𝓝 ((S').classMoment (S') (fun _=>d) x T)):=by
    intro T
    let Q(i):= fad (W i) x; let Y' z:= (S').classMoment (S') (fun _=>d) z T; let v(i):= S.classMoment (K x') (fun _=>d) (rum (W i) x) (fun j=> J.U i d (T j)); let m(z:Points 2):=Read.maxProfile C z (fun j=>⟨d,T j⟩); let M(z):= ‖(m z).part (Glyph.slot 0)‖+‖(m z).part (Glyph.slot 1)‖; let o:=costHint
    have hu:x∈conf 2:=generic_conf _ hh
    have hQ:= rounds hq h x
    have hY:Tendsto (Y' ∘ Q) atTop (𝓝 (Y' x)):= (((S').class_smooth (S') H.smooth (fun i=>⟨d,T i⟩)).continuousOn.continuousAt ((conf_open 2).mem_nhds hu)).tendsto.comp hQ
    have he:Tendsto (M ∘ Q) atTop (𝓝 (M x)):= (((Read.profile_part_cont (S') H.smooth _ _).norm.add (Read.profile_part_cont (S') H.smooth _ _).norm).continuousAt ((conf_open 2).mem_nhds hu)).tendsto.comp hQ
    have hl:Tendsto (fun i=> v i-Y' (Q i)) atTop (𝓝 0):= by
       apply tendsto_zero_iff_norm_tendsto_zero.mpr
       apply squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) (g:=fun i=>o i+M (Q i)*o i)
       · filter_upwards [hQ.eventually ht,hQ.eventually ((genericOpen 2).mem_nhds hh),seat hq w hf R hv hs hy t x' hr] with i hi hk hL; exact hL x (mixed hq x i hk hi.2) hi
       simpa using cost_clears.add (he.mul cost_clears)
    convert hl.add hY using 1; swap; · simp [Y']
    simp only [Function.comp_apply,sub_add_cancel,v]
lemma rainbow (t:ℕ→Fin 2→(S').Field d) (z:Fin 2→(S').Field d) (hb:∀ j, Tendsto (fun i=> t i j) atTop (𝓝 (z j))) : Tendsto (fun i=> S.classMoment (K x') (fun _=>d) (rum (W i) x) (fun j=> J.U i d (t i j))) atTop (𝓝 ((S').classMoment (S') _ x z)):=by
    let P:= (fun _ : Fin 2=>d)
    let U:= PoleC C d; let B (i):= (S.classMoment (K x') P (rum (W i) x)).compLinearMap (fun _=> (J.U i d).toLinearMap)
    let Q(z: Fin 2→ (S').Field d)(j:Fin 2→ PegC C d):= ∏ a: Fin 2, U.repr (z a) (j a);
    have he (A:MultilinearMap ℂ (fun _ : Fin 2=> (S').Field d) ℂ) (z:Fin 2→ (S').Field d): A z=∑ j:Fin 2→ PegC C d,Q z j * A (fun i=> U (j i)):=by
       have hx : z= fun i=> ∑ k, U.repr (z i) k • U k:= funext fun i=> (U.sum_repr _).symm
       conv_lhs=>rw[hx];
       rw[MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun i _=> A.map_smul_univ _ _
    change Tendsto (fun i=> B i (t i)) atTop (𝓝 ((S').classMoment (S') P x z))
    conv=> arg 1; intro i; rw[he]
    rw [he _ z]; apply tendsto_finsetSum _; intro j hj
    refine Tendsto.mul ?_ (greens hq w hf R hv hs hy x' hr h hh ht j)
    apply tendsto_finsetProd _; intro i hi; exact (((U.coord (j i)).continuous_of_finiteDimensional).continuousAt.tendsto).comp (hb i)
end YM.Trace.Verse
