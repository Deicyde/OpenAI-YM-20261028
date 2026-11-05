import YM.FullVolume.E6.Ques
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
variable {E' E₀:Type}[NormedAddCommGroup E'][NormedSpace ℝ E'][NormedAddCommGroup E₀][NormedSpace ℝ E₀]
private lemma trailing (X : E→ E')(a b:E)(k:ℕ): iteratedFDeriv ℝ k (fun y=> X (y+a)) b=iteratedFDeriv ℝ k X (b+a):= iteratedFDeriv_comp_add_right ..
private lemma shifted {F:E→ E'}(h:Brush j b a F p): Brush j b a (fun y=> F (y+p)) 0:=by
    have hx : ContDiffAt ℝ (↑j) F (0+p):= by simpa using h.smooth
    exact ⟨hx.comp 0 (f:=fun y=> y+p) (contDiffAt_id.add contDiffAt_const),h.pos,fun i hi=> by rw [normJ,trailing,zero_add]; exact h.order i hi⟩
private lemma shunted {F:E→ Config G c}(h:Mode F p j a)(L:E' →L[ℝ] E)(hp:‖L‖≤1): Mode (fun y=> F (L y+p)) 0 j a:=by
    refine ⟨h.pos,fun i=>?_⟩
    let Z y:= G.mat (F (y+p) i); have hg:Brush j (royalty G) a Z (L 0):= by rw [map_zero]; exact shifted (h.atLink i)
    exact (Brush.reading L hg hp).climb le_rfl (by rw [mul_one])
private lemma downhill {g:E → E₀}(h: ContDiffAt ℝ (↑j) g p)(L: E' →L[ℝ] E)(a: Fin j → E') : iteratedFDeriv ℝ j (fun x=> g (L x+p)) 0 a= iteratedFDeriv ℝ j g p (fun i=> L (a i)) :=by
     let u y:=g (y+p); have hg : ContDiffAt ℝ (↑j) u (L 0):= ContDiffAt.comp _ (g:=g) (f:=fun y=>y+p) (by rw [map_zero,zero_add]; exact h) (contDiffAt_id.add contDiffAt_const)
     change iteratedFDeriv ℝ j (u ∘ L) _ a=_; rw [linear_pull L hg,ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]; unfold u; rw [trailing,zero_add]
private def normal (v:E):E:= ‖v‖⁻¹ • v
private lemma normal_pay (v:E):‖normal v‖≤1:=by
     by_cases he:v=0; simp [normal,he]
     have hp:0< ‖v‖:= norm_pos_iff.mpr he; unfold normal; rw [norm_smul,Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hp.ne']
private lemma normed (v:E): ‖v‖ • normal v=v:=by
     by_cases he:v=0
     · simp [normal,he]
     · exact smul_inv_smul₀ (norm_pos_iff.mpr he|>.ne') _ -- syntax
private lemma devise (v:Fin j→ E) : let t:ℝ:= j+1; ∃ L:(Fin j→ℝ)→L[ℝ] E, ‖L‖ ≤ 1 ∧ ∃ a : Fin j→ Fin j→ℝ,∀ i,L (a i)=v i ∧ ‖a i‖= t*‖v i‖:=by
    intro t; let X:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin j=>ℝ); let V i: (Fin j→ℝ)→L[ℝ] E:= (X i).smulRight (normal (v i)); let L:= t⁻¹ • ∑ i,V i; have hp:0<t:=add_pos_of_nonneg_of_pos (by positivity) zero_lt_one; let z (i:Fin j) : Fin j→ℝ := Pi.single i (t*‖v i‖)
    have hh (x:Fin j→ℝ) i:(V i) x=x i • normal (v i):= rfl
    have ht:‖L‖≤1:=by
       unfold L; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]; refine le_trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hp.le)) (Eq.le (inv_mul_cancel₀ hp.ne')); refine le_trans (norm_sum_le ..) ?_
       apply (sum_le_sum (g:=fun _=>1) (fun i _=>?_)).trans
       · simp only [sum_const, nsmul_eq_mul, card_univ,Fintype.card_fin,mul_one]; exact le_add_of_nonneg_right zero_le_one
       apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [hh,norm_smul,mul_comm 1]; exact mul_le_mul (norm_le_pi_norm x i) (normal_pay _) (norm_nonneg _) (norm_nonneg _)
    refine ⟨L,ht,z,fun i=>⟨?_,by unfold z; rw [Pi.norm_single,Real.norm_of_nonneg (by positivity)]⟩⟩
    unfold L; rw [_root_.smul_apply, _root_.sum_apply,sum_eq_single i];
    · rw [hh]; unfold z; simp only [Pi.single_eq_same,smul_smul,inv_mul_cancel_left₀ hp.ne',normed]
    · intro k _ he; rw [hh]; unfold z; rw [Pi.single_eq_of_ne he,zero_smul]
    simp
private lemma highdowns {F: Config G c → ℝ}{a b:ℝ}{U:E→ Config G c}(h:Mode U p j a)(hg:ContDiffAt ℝ (↑j:WithTop ℕ∞) (F ∘ U) p) (hb:0 ≤ b) (k:ℕ)(he:k≤j) (hv:∀ V: (Fin k→ℝ)→ Config G c,Mode V 0 j a → V 0=U p → ‖iteratedFDeriv ℝ k (F ∘ V) 0‖ ≤ b/ (k+1:ℝ)^k) : ‖iteratedFDeriv ℝ k (F ∘ U) p‖≤ b:=by
     apply ContinuousMultilinearMap.opNorm_le_bound hb; intro v; obtain ⟨L,hL,u,hu⟩:=devise v
     let X y:= U (L y+p); let q:= iteratedFDeriv ℝ k (F ∘ X) 0
     have hq:q u=iteratedFDeriv ℝ k (F ∘ U) p v:= Eq.trans (downhill (p:=p) (hg.of_le (Nat.cast_le.mpr he)) L u) (congr_arg _ (funext fun i=> (hu i).1))
     rw [← hq]; apply le_trans (q.le_of_opNorm_le (hv X (shunted h L hL) (by simp [X])) u) ?_; simp_rw [(fun i=> (hu i).2), prod_mul_distrib, prod_const,card_univ,Fintype.card_fin]; rw [← mul_assoc, div_mul_cancel₀ _ (by positivity)]
set_option linter.unusedVariables false
variable {F H:ℕ→ Config G c →ℝ}{X: Config G c→Prop}
-- extract i bad at ANY support without pretending dependence on nearby ball.
lemma recover (hv:∀ V:ℕ→ Config G c, Tendsto (fun i=> F i (V i)-H i (V i)) atTop (𝓝 0)) (b:ℝ)(hb:0<b) :∀ᶠ i in atTop, ∀ u, ‖F i u-H i u‖≤b:=by
    by_contra hh; choose! g hg using fun i (hi:¬ ∀ u,‖F i u-H i u‖≤b)=> Classical.not_forall.mp hi
    exact hh (( (hv g).norm.eventually (gt_mem_nhds (by rwa [norm_zero] : ‖(0:ℝ)‖ < b))).mono (fun i hi=> Classical.byContradiction fun h=> hg i h (le_of_lt hi))) -- not_eventually_not
lemma boots (h:Nonempty {x|X x}) (ha:0≤a) (hx:∀ i V,X V→∃ b d, Ore V (F i) a b j∧ Ore V (H i) a d j)
    (hv:∀ k:ℕ,k≤j→∀ V:ℕ→ (Fin k→ℝ)→ Config G c,(∀ i,Mode (V i) 0 j a)→(∀ i,X (V i 0)) → Tendsto (fun i=>iteratedFDeriv ℝ k (fun y=> F i (V i y)) 0-iteratedFDeriv ℝ k (fun y=>H i (V i y)) 0) atTop (𝓝 0))
    (b:ℝ)(hb:0<b):∀ᶠ n in atTop,∀ V, X V→ Ore V (fun i=> F n i-H n i) a b j:=by
    let g i(u:Config G c):= F i u-H i u
    let step(k:ℕ):= (Fin k→ℝ)→ Config G c
    have h' i E (_:NormedAddCommGroup E) (_:NormedSpace ℝ E) (_:FiniteDimensional ℝ E) (x:E)(U:E→ Config G c)(hU:X (U x))(hp:Mode U x j a): ContDiffAt ℝ (↑j) (F i∘U) x ∧ ContDiffAt ℝ (↑j) (H i∘U) x:=by
         obtain ⟨b,d,h,h'⟩:=hx i (U x) hU; exact ⟨(h E U x rfl hp).smooth,(h' E U x rfl hp).smooth⟩
    have hh (k:ℕ)(he:k≤j):∀ᶠ n in atTop,∀ U:(Fin k→ℝ)→ Config G c,Mode U 0 j a → X (U 0)→ normJ k (g n ∘ U) 0 ≤ b/ (k+1:ℝ)^k:=by
          let u:=b/(k+1:ℝ)^k; have hu:0<u:=by unfold u; positivity
          let Z:= {V : (Fin k→ℝ)→ Config G c // Mode V 0 j a∧ X (V 0)}
          obtain ⟨V,hV⟩:= Set.nonempty_coe_sort.mp h
          have p:Nonempty Z :=⟨⟨fun _=> V, ⟨ha,fun i=> a_oneB _ _ ha⟩,hV⟩⟩
          have hi :∀ᶠ n in atTop, ∀ z:Z,normJ k (g n ∘ z.val) 0≤u:=by
              by_contra hz; let ψ n (z:Z):= normJ k (g n ∘ z.val) 0
              choose! A HA using fun n (hn:¬∀ z:Z, ψ n z≤u)=> Classical.not_forall.mp hn
              have H₀ n:iteratedFDeriv ℝ k (g n ∘ (A n).val) 0= iteratedFDeriv ℝ k (F n ∘ (A n).val) 0 - iteratedFDeriv ℝ k (H n ∘ (A n).val) 0:=by
                    obtain ⟨s,t⟩:= h' n (Fin k→ℝ) inferInstance inferInstance inferInstance 0 (A n).val (A n|>.2.2) (A n|>.2.1); exact iteratedFDeriv_sub_apply (s.of_le (Nat.cast_le.mpr he)) (t.of_le (Nat.cast_le.mpr he))
              have h :Tendsto (fun n=>normJ k (g n ∘ (A n).val) 0) atTop (𝓝 0):=by
                    unfold normJ; simp_rw [H₀]; rw [← norm_zero (E:=Tensor.T (Fin k→ℝ) ℝ k)]; exact (hv k he (fun i=>(A i).val) (fun i=>(A i).2.1) (fun i=>(A i).2.2)).norm
              exact hz ((h.eventually (gt_mem_nhds hu)).mono fun i hi=> Classical.byContradiction fun h'=> HA i h' hi.le)
          exact hi.mono fun i hi U hU h=>hi ⟨U,hU,h⟩
    filter_upwards [eventually_all_finset (Finset.range (j+1))|>.mpr (fun i hi=> hh i (by simpa using hi))] with i hi
    intro V hV E _ _ _ U p hp hf; obtain ⟨hP,hG⟩:= h' i E inferInstance inferInstance inferInstance p U (hp.symm ▸ hV) hf; refine ⟨hP.sub hG,zero_le_one,fun k hk=>?_⟩
    rw [one_pow,mul_one]; exact highdowns (F:=g i) hf (hP.sub hG : ContDiffAt ℝ (↑j) (g i ∘ U) p) hb.le k hk (fun V' hV' he=> hi k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) _ hV' ((he.trans hp).symm ▸ hV))
end YM.ConnectedActivityE6.Lim
