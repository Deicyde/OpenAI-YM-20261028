import YM.FullVolume.Mark.Hinge
import YM.MergeProof.Largo
import YM.MergeProof.Meringue




/-!
# ONE shared linear column family step

Coarse reference coordinate isn't obtained by fitting an expectation.
Rebase using injectivity of the **previous** readout, spend the atoms on
the *complete* column, then choose once and linearly combine the entire
paid column, incl forced parts. Necessary for a cone step: bounds are in
terms of *current* primary size (and remainders), not the sum of unsubtracted
uses of possibly huge original coefficients at earlier bases. Reserve K,
roomCost and Bank for true swollen costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Lattice Wilson RG Source Function Filter Set MeasureTheory Bid Labels Extra.Histories Motion PhysicalNext.Repeat Lotus
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d}
variable (B : SectionData F) (H : History G) (N p : ℕ) (A : Hol G)

variable (W: Worth)
omit A in
private theorem blast_march (m : ℕ) {f : F.Coeff → Config G (H.S.side (m+1) p) → ℂ} (h : IsLinearMap ℂ f)
    (hF : ∀ v, Integrable (f v) (prior G _)) : IsLinearMap ℂ fun x => blast H N p m d (f x) := by
  constructor
  · intro x y
    simp only [blast,h.map_add,StepData.push_add (H.levels.transition_mass ..) _ _ (hF _) (hF _),smul_add]
  intro c y
  simp only [blast,h.map_smul,StepData.push_smul _ _ _ _ (hF _), smul_comm c]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 960000 in
theorem motor (m : ℕ) (V : Voice F H p (m+1)) {η C : ℝ}
    (hq : Heard B H N p A (m+1) V) (hw : roomCost H.levels W)
    (hb : Bank W H.levels) (T : Heading F)
    (D : GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(Xk : Set Wing){t : ℝ}
    (R₀:Tool F H N p m)(hT₀:Tool.Cap R₀ B A W D T C η t Xk) (hr : Chorus H N p (m+1) V)
    {U:Desk G (H.S.side (m+1) p)}
    (hu:Well (H.rep N p (m+1)) U (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))):
    let R:= measure hq R₀.up hu
    ∃ Q : Voice F H p m, (∀ v,Q.plays v = Gram.point R₀ R (V.index v)) ∧ (Heard B H N p A m Q ∧ Responds B H N p W m V Q ∧ Chorus H N p m Q∧ Carol B H N p m D V Q t) := by
  classical
  intro R₁; let L:= H.S.block m; have h:= hT₀.shines; have ht:= hT₀.copies; have he:= hT₀.budget; have hm:=hT₀.late; have hD:=hT₀.dish; have hxt:=hT₀.toll;have hT:=hT₀.good; have hk:= hT₀.tote; have hN(u):= (Tour.bright H h N p (m+1) hm u).ne'
  let f (v) := (V.plays v).density 0 B (H.rep N p (m+1))
  have hf (v) : Integrable (f v) (prior G _) :=
    play_integrable H N h hm (hq.earns v).1 (hq.earns v).2
  let P := fun x => blast H N p m d (f x)
  have hP : IsLinearMap ℂ P := blast_march H N p m hq.values hf
  have hM (v) (y) : dance y (P v) = P (Motion.patch F y v) := by
    rw [← show blast H N p m d (dance y (f v))= dance y (P v) from blast_dance H N p m d y (f v) (hf v)]
    rw [show dance y (f v) = f (Motion.patch F y v) from hq.travels ..]

  let s := (H.levels.params (m+1)).columns

  let R := H.rep N p m
  let Dm (z) := F.coeffSize (vowel F L (F.core z))
  let c := C + η*s
  let ε := η*(1+s)
  have hS : 1 ≤ s := (H.levels.params (m+1)).columns_ge
  have hη := he.epsilon
  have hc' := he.cost
  have hs : 0 ≤ s := by linarith
  have hcc : C ≤ c := le_add_of_nonneg_right (by positivity)
  have hc : 0 ≤ c := by linarith
  have hε : 0≤ε := by unfold ε; positivity
  let J := Size.axis F
  let j i:= V.index.symm (J i)
  let Pm i:= V.plays (j i);let E:=H.rep N p (m+1); let x' :=s
  have hv i: V.index (j i)=J i:= V.index.apply_symm_apply _
  have hxC i:(Pm i).x=J i:=(hq.currents _).trans (hv i)
  let Z₀ i:= R₀.shot i (Coin.uses (R₁.scythe i))
  have hd' (i : F.Index) : Span B H N p m A (Z₀ i) ((Pm i).exponentialEntry 0 B E) (profile E.activities (Pm i).forced) (J i 0) D Xk (f (j i)) (T.leads L (J i))
      (ε * F.coeffSize (F.core (J i))) (c*Dm (J i)) (t+2*s) := by
    let v := V.index.symm (J i)
    have hh : V.index v = J i := V.index.apply_symm_apply _
    let q:= R₁.g (J i)
    have H':= R₀.recoil hT₀ hu i q; let Hx:= (R₀.shot i (Coin.uses q));change Span _ _ _ _ _ _ _ _ _ _ _ _ ((book _ _).density _ _ _) _ (η*(_+‖q‖)) (C*_+η*‖q‖) _ at H'
    let p' :=Pm i;have hp: Coin.uses q=capture p' R₀.up :=rfl
    have h' : ‖q‖ ≤ V.charge v:=(Coin.wealths (duly hq R₀.up hu v)).mpr (alongPay hu R₀.up p' (hq.earns v).1 (hq.earns v).2)
    have h:Span B H N p m A (Z₀ i) (p'.exponentialEntry 0 B E) (profile E.activities p'.forced) (J i 0) D Xk (p'.density 0 B E) (T.leads L (J i)) (η*(F.coeffSize (F.core (J i))+‖q‖)) (C*Dm (J i)+η*‖q‖) (t+2*‖q‖):= by
        let S:= book p'.x (capture p' R₀.up)
        have Hhf : book (J i) (Coin.uses q)= S:=by rw [hp,← hxC]
        have hP:Span B H N p m A (Z₀ i) (S.exponentialEntry 0 B E) (profile E.activities S.forced) (J i 0) D Xk (S.density 0 B E) (T.leads L (J i)) (η*(F.coeffSize (F.core (J i))+‖q‖)) (C*Dm (J i)+η*‖q‖) (t+2*‖q‖):=by rw [←Hhf]; exact H'
        rw [show S.exponentialEntry 0 B E = _ from expo p' R₀.up B (hq.earns v).1, show profile E.activities S.forced=_ from profited p' R₀.up, show S.density 0 B E= _ from Matric.pays p' R₀.up B (hq.earns v).1 (hq.earns v).2 (h.represents N p (m+1) hm).good] at hP; exact hP
    have hu : ‖q‖ ≤ s * F.coeffSize (F.core (J i)) := hh ▸ h'.trans (hq.cone v)
    have hz : F.coeffSize (F.core (J i)) ≤ Dm (J i) := (Work.G08.size_vowel F L _).1
    refine h.weaken ?_ ?_ (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hu.trans ?_) zero_le_two))
    · exact (mul_le_mul_of_nonneg_left (add_le_add_right hu _) hη).trans_eq (by unfold ε J; ring)
    · exact (add_le_add_right (mul_le_mul_of_nonneg_left (le_trans hu (mul_le_mul_of_nonneg_left hz hs)) hη) _).trans_eq
        (by unfold c Dm L J; ring)
    apply mul_le_of_le_one_right hs; unfold J;rw [Size.core_axis];split; next h=> simp [Frame.coeffSize]
    next h=> rw [Size.size_axis]
  have h₀ i:= (hd' i).earns; have hβ i:= (hd' i).songs
  let X i:= (Z₀ i).x
  let Fm (m':Motion) : E.activities.Moves m'.1 ((H.levels.clock.op _ p).ratio.embed 0):= (h.represents N p (m+1) hm).good.labels.moves _ _|>.some
  let u₀ (m':Motion): R.activities.Moves m'.1 0:= R₀.whirl m'
  let Q i m:= Planned.GuardedAtom.audition (u₀ m) (Z₀ i)
  let y₀ := Real.sqrt (H.levels.clock.forcedAllowance m)
  have HX(i m'): F.coeffSize (Motion.patch F m' (X i)- Motion.patch F m' (T.leads L (J i)))≤ε * F.coeffSize (F.core (J i)):= by rw [← Planned.GuardedAtom.patch_sub]; exact (patch_cost _ _ _).trans (h₀ _).leadP
  have hi(i m'): (Q i m').x=Motion.patch F m' (X i) ∧ (Q i m').Format 0 A R ∧ (Q i m').remBound 0 R y₀ (c*Dm (J i)) ∧ (Q i m').density 0 B R=dance m' (P (j i)):=by
     obtain ⟨a,b,hq,hF⟩:=(h₀ i).future
     obtain ⟨hz,hx,hP,hβ⟩:= Planned.GuardedAtom.audition_receipt m' (u₀ m') ((by decide : 2 ≤ 4).trans (Next.Foundations.actual_side_ge H.S m p)) hT (h₀ i).format hq
     exact ⟨hz,hx,hP.bound hF,hβ.trans (congr_arg (dance m') (h₀ _).agrees)⟩
  have hF i m':= (hi i m').2.1; have hY i m':= (hi i m').2.2.1; have hQ i m':= (hi i m').1; have hU i m':= (hi i m').2.2.2
  let O : Tally F → Coefficient F _ := fun j => Q j.2 j.1
  let Y : F.Coeff →ₗ[ℂ] Tally F → ℂ := (chips F).comp V.index.toLinearMap
  let Z : F.Coeff → Coefficient F _ := pencil (code (Tally F)) O Y
  let a v := c * orbitCost F * Dm (V.index v)
  let y := Real.sqrt (H.levels.clock.forcedAllowance m)
  have hy : 0<y := Real.sqrt_pos.2 (forcedPos ..)
  have hy' := (h.represents N p m hm.le).good
  have hb' (v) : (Z v).Format 0 A R ∧ (Z v).remBound 0 R y (a v) := by
    let t (j : Tally F) := c*Dm (J j.2)
    have h := pencil_cost (code _) O Y (X:=t) hy (fun j => ⟨hF j.2 j.1,hY j.2 j.1⟩) v
    exact ⟨h.1,rem_mono h.2 (residual_bill F L c hc (V.index v))⟩
  have hZ (v) : (Z v).x = repaint F X (V.index v) := by
    unfold Z
    rw [pencil_x]
    exact Finset.sum_congr rfl fun i _ => congr_arg (chips F (V.index v) i • ·) (hQ ..)
  have hp (v) : (Z v).density 0 B R=P v := by
    let K := (IsLinearMap.mk' P hP).comp V.index.symm.toLinearMap
    have hh (v) (y) : dance y (K v)=K (Motion.patch F y v) := by
      change dance y (P _)=P _
      rw [hM]; apply congr_arg
      apply V.index.injective; rw [← hq.moves]; simp
    funext x
    have hi := field_same F K hh (V.index v) x
    unfold Z
    rw [pencil_density (code _) O Y hy' hy (X:=fun j => c*Dm (J j.2)) (fun j => hY j.2 j.1)]
    refine (Finset.sum_congr rfl (g:=fun i : Tally F => chips F (V.index v) i *
        dance i.1 (K (J i.2)) x) fun i _ => ?_).trans (hi.trans ?_)
    · exact congr_arg ((Y v i) * ·) (congr_fun (hU i.2 i.1) x)
    change P (V.index.symm (V.index v)) x= P v x; rw [LinearEquiv.symm_apply_apply]

  have hI (v) : F.coeffSize ((Z v).x - T.leads L (V.index v)) ≤
      barunit L * F.coeffSize (F.core (V.index v)) := calc
    _ ≤ ε*orbitCost F*F.coeffSize (F.core (V.index v)) := by
      rw [hZ]; exact budgets_orbit F L T X (V.index v) ε hε (fun i => HX i.2 i.1)
    _ ≤ _ := mul_le_mul_of_nonneg_right he.tiny (Work.G08.size_nonneg ..)
  have ht' (v) : direction H W m F (Z v).x (V.plays v).x (a v) (V.charge v) := by
    rw [hq.currents]
    have ho : 0 ≤ V.charge v := rem_nonneg (hq.earns v).2
    have hg : 0 ≤ barunit L := by
      have hl : (0 : ℝ) ≤ L.val := by positivity
      unfold barunit puffs; positivity
    refine ⟨rem_nonneg (hb' v).2,ho,T.map,fun x => ?_, (hI v).trans ?_,?_⟩
    · have hb : C ≤ W.K (H.levels.clock.J (m+1)) :=
        le_trans (hcc.trans (le_mul_of_one_le_right hc (orbitCost_one_le F))) he.funds
      have hz := mul_le_mul_of_nonneg_right hb (Work.G08.size_nonneg F x)
      exact ⟨((ht.heading x).1).trans hz,((ht.heading x).2).trans hz,(T.core_comm x).symm⟩
    · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ho) hg
    change c * orbitCost F * Dm (V.index v) ≤ _
    refine le_trans (mul_le_mul_of_nonneg_right he.funds (Work.G08.size_nonneg F _)) ?_
    change _*Dm _ ≤ _*F.coeffSize (F.core (vowel F L _))+_
    rw [Work.G08.core_vowel]
    exact le_add_of_nonneg_right (mul_nonneg hg ho)

  have hback (v) := Work.G08.cone_step W H hw hb m F _ _ _ _ (ht' v) (show V.charge v ≤
    s * F.coeffSize (F.core (V.plays v).x) from (hq.currents v).symm ▸ hq.cone v)
  have hBook : Ledger F _ Z := pencil_ledger ..
  let Ψ := IsLinearMap.mk' _ hBook.x
  have hΨ : Injective Ψ := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have ha := (hback v).2.1
    rw [show (Z v).x=0 from hv, hq.currents] at ha
    apply V.index.injective
    rw [map_zero]
    exact Work.G08.size_separates F _ (by simpa [Frame.coeffSize] using ha)
  let out : Voice F H p m := ⟨Z,a,LinearEquiv.ofBijective Ψ ⟨hΨ, LinearMap.injective_iff_surjective.mp hΨ⟩⟩
  let M₀(v) := profile R.activities (Z v).forced
  have hMx(v): M₀ v= ∑ j:Tally F,Y v j • floatUp j.1 0 (profile R.activities (Z₀ j.2).forced):=by
      funext p' U; have h:= profile_merge (code _) (fun j:Tally F=> (Extra.Histories.stretch (Y v j) (Q j.2 j.1))) hy (fun j=> stretch_rem _ (hY j.2 j.1)) Summable.of_finite p' U
      rw [show M₀ v p' U= _ from h.tsum_eq.symm,tsum_fintype]; simp only [Finset.sum_apply]
      exact Finset.sum_congr rfl (fun i _=> congr_fun (congr_fun ((profile_scale ..).trans (congr_arg (fun p=>(Y v i) • p) (foyer i.1 0 (u₀ i.1) (Z₀ i.2)))) _) _)
  -- union dependent turning (no accidental O push reuse)
  let X': Set Wing:= ⋃ i:Motion,(Wing.labelRoute (Fm i)) '' Xk
  have hhQ(z:Tally F): let T':= V.index.symm (Motion.patch F z.1 (J z.2)); let U:=V.plays T'; Tale X' 0 0 ((↑L.val:ℂ)^d) (U.exponentialEntry 0 B E) (profile E.activities U.forced) (profile R.activities (O z).forced) ((Motion.patch F z.1 (J z.2)) 0) (t+2*s) (c*Dm (J z.2)) D:=by
     intro T' U; let i:=z.2; let m':=z.1; let V':Site (H.S.side (m+1) p):= (H.levels.clock.op m p).ratio.embed 0
     have he: V'= 0:= Motion.embed_origin _
     have hAA: X'≥ (Wing.labelRoute (Fm z.1)) '' Xk:=subset_iUnion (fun i:Motion=> (Wing.labelRoute (Fm i)) '' Xk) z.1
     have hmV:T'=Motion.patch F z.1 (j z.2):= V.index.injective (by rw [← hq.moves]; change V.index (V.index.symm _)= _;simp [j])
     have hW:= (hβ i).gain hD z.1 0 (Fm z.1) (by unfold Motion.scalar;split<;>simp)
     have hp := hW.climb hAA le_rfl le_rfl
     rw [show U= V.plays (Motion.patch F z.1 (j z.2)) from congr_arg _ hmV]
     rw [← hr.pages, show profile R.activities (O z).forced = _ from foyer z.1 0 (u₀ z.1) (Z₀ z.2), ← chanting B H N p _ A V hT hq hr h hm hN] -- want profile O z = floatUp z
     rw [show (H.levels.clock.op _ p).ratio.embed 0=0 from he] at hp
     simp only [affine,Signed.act_zero,zero_add] at hp
     rw [show Motion.patch F z.1 (J _) 0 = scalar z.1 (J i 0) from ?_]; exact hp
     unfold Motion.patch scalar; split <;>simp only [Pi.star_apply, Push.Local.act_at_zero] <;> rfl
  refine ⟨out,fun v=> rfl, ⟨hBook,hb',fun _ => rfl,fun v => (hback v).1,?_,fun v x => ?_,?_, ?_, ?_⟩,⟨hp,ht'⟩,?_,?_⟩
  · intro i j
    change a (i+j) ≤ a i + a j
    unfold a Dm
    rw [map_add,map_add,← mul_add,show vowel F L (F.core (V.index i) + F.core (V.index j)) =
      vowel F L (F.core (V.index i))+vowel F L (F.core (V.index j)) from by ext; simp [vowel,mul_add]]
    exact mul_le_mul_of_nonneg_left (Size.add F _ _) (mul_nonneg hc (zero_le_one.trans (orbitCost_one_le _)))
  · change Motion.patch F x (Z v).x=(Z _).x
    rw [hZ,hZ,repainted_eq,hq.moves]
  · change (Z (unitVec F H N)).x = _
    have hc := hI (unitVec F H N)
    rw [hq.unit,show F.core (unitVec F H (m+1))=0 by simp [unitVec,Size.unit_core]] at hc
    rw [show (Z (unitVec F H N)).x = T.leads L (unitVec F H (m+1)) from sub_eq_zero.mp (Work.G08.size_separates _ _ (by simpa [Frame.coeffSize] using hc))]
    change T.map (vowel F L _) = _
    rw [show vowel F L (unitVec F H (m+1)) = unitVec F H m from unit_vowel ..]; simp [unitVec,T.unit]
  · change IsLinearMap ℂ (fun v => (Z v).density 0 B R)
    simpa only [hp] using hP
  · intro v x
    change dance x ((Z v).density 0 B R)=(Z _).density 0 B R
    rw [hp,hp,hM]
  · refine ⟨fun v z=>?_⟩; change floatUp z 0 (M₀ v)= M₀ _
    rw [hMx,hMx]; simp only [Y,LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, ← hq.moves]; exact concert z (V.index v) (fun i=> profile R.activities (Z₀ i).forced) -- Y,v infer
  refine ⟨X', Set.finite_iUnion fun m=> hk.image _,?_⟩
  intro v I R' x'
  let α(z:Tally F):= Motion.patch F z.1 (J z.2); let f z:= V.plays (V.index.symm (α z)); let e' z:= Extra.Histories.stretch (Y v z) (O z)

  have htP (z:Tally F):= Tale.travel (hhQ z) (Y v z)

  have hM₀(z:Tally F): Tale X' 0 0 ((↑L.val:ℂ)^d) (Y v z • (f z).exponentialEntry 0 B E) (Y v z • profile E.activities (f z).forced) (profile R.activities (e' z).forced) (Y v z * α z 0) (‖Y v z‖*(t+2*s)) (‖Y v z‖*(c*Dm (J z.2))) D:=by
     rw [show (e' z).forced= Y v z • (O z).forced from rfl, profile_scale]; exact htP z
  -- input series just linear maps by fixing.Complex.V actual
  apply Tale.upon hD hM₀
  · let g':= (IsLinearMap.mk' _ (expoLinear (T:=B) _ _ hq.book (fun i=> (hq.earns i).2))).comp V.index.symm.toLinearMap
    intro Ux

    have hyx: I.exponentialEntry 0 B R' Ux= (g' x') Ux:=by unfold I; change _=(V.plays (V.index.symm x')).exponentialEntry 0 B E Ux; rw [show V.index.symm x'=v from V.index.symm_apply_apply _]
    rw [hyx, ← fixing F g' x']; simp only [Finset.sum_apply]; exact hasSum_fintype _
  · let g'(v):= profile E.activities (V.plays v).forced
    let S:=(IsLinearMap.mk' g' (inkL V.plays V.charge hq.book (fun i=> (hq.earns i).2))).comp V.index.symm.toLinearMap
    intro i Ux
    have hyx: profile R'.activities I.forced i Ux= S x' i Ux:=by change _=g' (V.index.symm x') i Ux; rw [show V.index.symm x'=v from V.index.symm_apply_apply _]
    rw [hyx,← fixing F S x']; simp only [Finset.sum_apply]; exact hasSum_fintype _
  · intro j U
    exact profile_merge (code _) e' hy (fun j=> stretch_rem (Y v j) (hY j.2 j.1)) Summable.of_finite j U -- order
  · have hxL : x'=∑ z:Tally F,Y v z • α z:= (fixing F LinearMap.id x').symm -- order
    -- rw hxL only RHS
    rw [hxL]; simp only [Finset.sum_apply]; exact hasSum_fintype (fun z=> Y v z*α z 0)
  · refine ⟨fun i=> mul_nonneg (norm_nonneg _) (by positivity),Summable.of_finite,?_⟩; rw [tsum_fintype,← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (rip ..) (by positivity)
  refine ⟨fun j=> mul_nonneg (norm_nonneg _) (rem_nonneg (hY j.2 j.1)), Summable.of_finite,?_⟩; rw [tsum_fintype]; exact residual_bill F L c hc _
end YM.MergeProof.Matric
