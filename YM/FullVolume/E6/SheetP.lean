import YM.FullVolume.E6.Master
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
variable {M:Bank}(I:Depot Q o x μ L C₀ K){χ: Chi}(Y:∀ n,Station M χ (I n) j){n:ℕ}{X:Coat (K n).tubes F}
section
variable [FiniteDimensional ℝ E]{V:E→ Config G c}(hx:X.x=x)(hχ:X.χ=χ)(hK:X.width=o.K)(hM:X.manifest)(ht:Mode V p j M.v)(hg:V p=X.V)
include hx hχ hK hM I Y ht hg
lemma destiny (z:Air f G)(i : Molecule S)(k:Finset ℕ) :
    let f y:= steer X M.A (worldZ X (K n).kin.beta z) (V y); let g(y:E):= course X M.A (K n).kin.beta z (V y)
    (fun y:E=> Polar.floating (vary X (V y)) o.a (K n).kin W Q.table (g y) k Q.halo i)=ᶠ[𝓝 p] fun y=> ∏ b∈i, Polar.ember (vary X (V y)) o.a (K n).kin W Q.table (f y) (X.input (worldZ X (K n).kin.beta z)) (g y) k Q.halo b:=by
       intro f g; let D:= (Y n).fleets; have hr:= ((D.M.rays F X hx hK hχ hM E V p hg ht).2 z).1
       filter_upwards [hr.patch] with y hy; unfold Polar.floating; rw [hr.moving y]; apply prod_congr rfl; intro i _
       exact (plastic hy hr.pulse).reeled (show Room _ S _ (vary X (V y)).x from hx.symm ▸ (I n).laws.data.room) W Q.table k Q.halo (show Intake _ _ (vary X (V y)).x (K n).kin from hx.symm ▸ (I n).laws.intake) i _
variable {q:ℕ→ Head S→ℝ}
abbrev salaries (k:ℕ) (v:Molecule S) (n:ℕ)(q:ℕ→ Head S→ ℝ) := ∏ i∈ v,((2:ℝ)^k*q n i)
omit hx hχ hK hM I Y ht hg in
private lemma boundI(s:Molecule S):1+s.card≤ (2:ℝ)^s.card:=by
    have h (n:ℕ): 1+n≤ (2:ℝ)^n:=by induction n with
                                      | zero=>norm_num
                                      | succ n ih=> push_cast; rw [pow_succ]; have h' : (0:ℝ)≤n:= Nat.cast_nonneg _; linarith
    exact h _
lemma taxi (z:Air f G)(i : Molecule S)(k:Finset ℕ) (he:Coins M Q o χ j x K q) (hy:Healthy (Pressure.temp x) ((I n).unionP i) X.V): Brush j (salaries j i n q) 1 (fun y=> Polar.floating (vary X (V y)) o.a (K n).kin W Q.table (course X M.A (K n).kin.beta z (V y)) k Q.halo i) p:=by
    let f y:=steer X M.A (worldZ X (K n).kin.beta z) (V y);let g y:=course X M.A (K n).kin.beta z (V y); let C b y:=Polar.ember (vary X (V y)) o.a (K n).kin W Q.table (f y) (X.input (worldZ X (K n).kin.beta z)) (g y) k Q.halo b
    refine (Brush.all_prod i C (q n) (fun _=>1) ?_ |>.trim).shimmy (destiny I Y hx hχ hK hM ht hg z i k)|>.climb ?_ le_rfl
    · intro b h; exact he.regular n F X hx hK hχ hM k z b (Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem (I n).supportP h) hy) E V p hg ht
    simp only [sum_const,nsmul_eq_mul,salaries,prod_mul_distrib,prod_const, mul_one]
    rw [mul_comm _ (_^j)]; gcongr
    · exact prod_nonneg fun i _=> he.silver.value ..
    rw [← pow_mul,Nat.mul_comm,pow_mul]; gcongr; exact boundI i
lemma waving (y: F.Slice G × Air f G) (D:Finset (Bond f))(i:Molecule S)(he:Coins M Q o χ j x K q)(hy: Healthy (Pressure.temp x) ((I n).unionP i) X.V): Brush j ((1*salaries j i n q)*(1+(M.p*facescale D y.2 ^ M.K+1))^j) 1 (fun v=> rhythm D X (V v) M.A Q.table i (K n).kin W o.a Q.halo y) p:=
   (((((Y n).fleets.M.rays _ (X.wrapY y.1) hx hK hχ hM E V p hg ht).2 y.2).2 D|>.1).paints (taxi I Y (X:=X.wrapY y.1) hx hχ hK hM ht hg y.2 i (own i) he hy)).trim
end
structure Clubs (M:Bank)(I: Depot Q o x μ L C₀ K)(χ:Chi)(j:ℕ)(q:ℕ→ Molecule S→ℝ):Prop where
    value:Sparse q
    heavy : ∀ n (F:Forest S.ratio)(X:Coat (K n).tubes F), X.x=x→ X.width=o.K→ X.χ=χ→ X.manifest →∀ p,|X.attains (K n).kin Q.table W o.a (own p) Q.halo p|≤ q n p
    steady : ∀ n (F:Forest S.ratio)(X:Coat (K n).tubes F), X.x=x→ X.width=o.K→ X.χ=χ→ X.manifest →∀ i,Healthy (Pressure.temp x) ((I n).unionP i) X.V→∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](V:E→ Config G c)(p:E), Mode V p j M.v→ V p=X.V→Brush j (q n i) 1 (fun v=>bars (podium S G ((I n).unionP i) (radiusB x)) (vary X (V v)) i (K n).kin Q.table W o.a Q.halo) p
include I Y
lemma carded {q}(he:Coins M Q o χ j x K q):∃ w:ℕ→ Molecule S→ ℝ, Clubs M I χ j w:=by
    let v(I:Finset (Bond f)):= (lensS I G).card; let d:= M.K*j; let B:=payE o.eta o.gap o.ample (tubularPrice G L); let C (I:Finset (Bond f)):= (1+(I.card:ℝ)+v I+v I)^d*(1+(v I:ℝ)*(2*Real.exp (B*(d:ℝ)^2/2)))
    obtain ⟨b,hb⟩:= (Set.finite_range C).bddAbove; let L':=(M.p+2)^j; have hp:0≤M.p:= (Y 0).fleets.M.pos; have hl:0≤L':=pow_nonneg (by linarith) _; let s:=L'* |b|
    have hX:= he.silver.arbitrary; let r n i:= salaries j i n q; have hr:Sparse r:= ((he.silver.climb (show 0≤(2:ℝ)^j by positivity)).arbitrary)
    refine ⟨_,⟨hX.tug (hr.climb (show 0≤ s from mul_nonneg hl (abs_nonneg _))),?_,?_⟩⟩
    · intro n F X hx hK hχ hM p; refine ((show ‖X.attains (K n).kin Q.table W o.a (own p) Q.halo p‖ ≤ ∏ i∈p,q n i from ?_)).trans (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hl (abs_nonneg _)) (hr.value ..)))
      apply le_trans (norm_integral_le_integral_norm _); refine (integral_mono (((I n).integrated X hx hK hM (own p) p).norm) (integrable_const _) (g:=fun _=> ∏ i∈p,q n i) (fun y=>?_)).trans_eq (by simp)
      unfold Coat.body Coat.term ; rw [norm_prod]; exact prod_le_prod (fun i _=> norm_nonneg _) fun i _=> he.force n F (X.wrapY y.1) hx hK hχ hM (own p) y.2 i
    intro n F X hx hK hχ hM i hy E _ _ _ V p ht hg; let K':=(I n).unionP i; let D:= edgesM S K' (radiusB x); let m:=(F.order G).prod X.dice
    have hT:=(I n).laws.data.localP F X hx hK hM; let N:=(Y n).fleets.M; have hz := (N.rays F X hx hK hχ hM E V p hg ht).1
    let P:= fun z : Air f G=> facescale D z^d; let W' : Air f G→ ℝ:=fun z=> L'*r n i*P z
    obtain ⟨hm,hW⟩:=globes D hT.sails d; have hZ : Integrable (fun x:F.Slice G×Air f G=> W' x.2) m:= (hm.const_mul (L'*r n i)).comp_snd _
    let a x:= rhythm D X (V x) M.A Q.table i (K n).kin W o.a Q.halo
    have hX:= (boosts (I n) hx hM hK hz N.solid N.grants i D).1; refine (hX.buds (fun x=>W' x.snd) hZ zero_le_one ?_ (ae_of_all _ (fun x=> ?_))).shimmy (chutes (I n) hx hM hK hz N.solid N.grants i)
    · rw [integral_prod _ hZ]; simp only [W', integral_const_mul, integral_const, MeasureTheory.probReal_univ,one_smul]; have hx : ∫ z,P z ∂X.dice ≤ |b| := (hW.trans (hb (Set.mem_range_self (f:=C) D))).trans (le_abs_self _)
      apply (mul_le_mul_of_nonneg_left hx (mul_nonneg hl (hr.value ..))).trans; refine le_trans (le_of_eq ?_) (le_add_of_nonneg_left (Finset.prod_nonneg fun i _=>he.silver.value ..)); unfold s r; ring
    have hL:= waving I Y hx hχ hK hM ht hg x D i he hy
    apply hL.climb _ le_rfl; let y:= facescale D x.2; have hx:1≤y:= (expenses D _).1; have hw:1≤ y^M.K:= one_le_pow₀ hx
    change (1*r n i)*(1+(M.p*y^M.K+1))^j ≤ L'*r n i*y^d; rw [one_mul];
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (show 1+(M.p*y^M.K+1)≤(M.p+2)*y^M.K by linarith only [hw]) _) (hr.value ..)).trans_eq ?_; unfold L' d; rw [mul_pow,pow_mul]; ring
end YM.ConnectedActivityE6.Lim
