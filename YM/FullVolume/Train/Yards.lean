import YM.Next.FREE_KERNELS.Rack
import Mathlib.Analysis.Normed.Group.Tannery
/-! LevelD covariance through flying lengths.Dilation. Real momentum.ALL cuts.Depoly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.OnTrack
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid Train
open scoped Topology BigOperators ComplexConjugate
variable {G:Gauge} (A:Levels G) (x:Axis)
private lemma flight (i d) : flying A (d+1) i=(stageHop A i (flying A d (i+1))).land:=rfl
lemma far_mass (m) : Tendsto (fun d=> (flying A d m).mass.val) atTop atTop:=by
  have he (d m) : d+1≤(flying A d m).mass.val:=by
    induction d generalizing m with
    | zero=>exact le_refl 1
    | succ i ih=>
      rw [flight,Flight.land,Train.mass,PNat.mul_coe]; change _ ≤ (A.S.block m).val*(flying _ _ _).mass.val
      have hk:=Nat.mul_le_mul (A.S.block_large m) (ih (m+1)); omega
  exact tendsto_atTop_mono (fun i=> le_trans (Nat.le_succ i) (he i m)) tendsto_id
private def usd (i d) (p: Momentum):= yen ((flying A d i).drive x) (narrow (flying A d i).mass p)
private lemma exchange_lands (L M:Side)(p:Momentum):
    M.val • narrow (L*M) p=narrow L p ∧ narrow M (narrow L p)=narrow (L*M) p:=by
   have hM:=(side_ne M); have hL:=side_ne L
   constructor
   · ext1 i; rw [Pi.smul_apply,nsmul_eq_mul,narrow_apply,narrow_apply,mul_side_complex]; field_simp
   ext1 i; rw [narrow_apply,narrow_apply,narrow_apply,mul_side_complex]; field_simp
private lemma USD (i d:ℕ)(p):
    usd A x i (d+1) p =
      yen (pullLine (stageHop A i (Train.top _)).patch x) (narrow (A.S.block i) p)*
        usd A x (i+1) d (narrow (A.S.block i) p) :=by
  unfold usd yen; rw [flight,Flight.land]; simp_rw [Train.drive_links]
  let P:=(stageHop A i (Train.top _)).patch
  let L:=A.S.block i; let M:=(flying A d (i+1)).mass; let D:= (flying A d (i+1)).drive x; let F:=pullLine P x
  change (F (M.val • narrow (L*M) p)*D _) *(F (M.val • -narrow (L*M) p)*D _) = F _*F _*(D _*D _)
  rw [(exchange_lands L M p).1, (exchange_lands L M p).2, smul_neg,(exchange_lands L M p).1]
  change (F (narrow L p)*D (narrow (L*M) p))*(F (-narrow L p)*D (-narrow (L*M) p))= F (narrow L p)*F (-narrow L p)*(D _ *D _)
  ring
lemma ltd (P: Patch)(x:Axis)(p:Momentum)(hp:physical p): ‖pullLine P x p‖≤1:=by
    have he:= physical_iff p|>.mp hp
    unfold pullLine massFilter area; rw [norm_mul,norm_pow,norm_prod]
    refine mul_le_one₀ ?_ (norm_nonneg _) ((rail_height _ (p x)).trans_eq (by rw [he x,abs_zero,mul_zero, Real.exp_zero]))
    · apply pow_le_one₀ (Finset.prod_nonneg fun i _=>norm_nonneg _)
      apply Finset.prod_le_one (fun i _=> norm_nonneg _) (fun i _=>?_)
      exact (plank_height ..).trans_eq (by rw [he i,abs_zero,mul_zero, Real.exp_zero])
lemma sales (P:Patch)(x:Axis){p:Momentum}(hp:physical p): Silver (yen (pullLine P x) p) ∧ (yen (pullLine P x) p).re ≤ 1:=by
   have he : physical (-p):=by unfold physical; rw [star_neg,show star p=p from hp]
   refine ⟨?_,(Complex.re_le_norm _).trans (?_)⟩
   · have hm : star (pullLine P x p)=pullLine P x (-p) := by
        have hu := area_conj P.L p
        have ht := rail_bar P.L (p x)
        rw [show star p=p from hp] at hu
        rw [show star (p x)=p x from congr_arg (fun t:Momentum=>t x) hp] at ht
        unfold pullLine massFilter; rw [star_mul,star_pow,hu,ht,mul_comm]; rfl
     unfold yen; rw [←hm]; exact Silver.gram _
   unfold yen; rw [norm_mul]; exact mul_le_one₀ (ltd P x p hp) (norm_nonneg _) (ltd P x _ he)
private lemma swatch (i d:ℕ)(p:Momentum)(hp:physical p): (usd A x i (d+1) p).re ≤ (usd A x i d p).re:=by
   induction d generalizing i p with
   | zero=>
     rw [USD]; let q:= narrow (A.S.block i) p; have he:= sales (stageHop A i (Train.top _)).patch x (narrow_real _ hp: physical q)
     unfold usd
     have hk i r : yen ((flying A 0 i).drive x) r=1:=by rw [yen]; unfold Train.drive; simp only [flying,Train.mass,Train.smooth_top,rail_unit,one_mul]
     rw [hk,hk, mul_one]; exact he.2
   | succ d ih=>
     rw [USD A x i (d+1), USD A x i d]; let q:= narrow (A.S.block i) p; have hp': physical q := narrow_real _ hp
     let L:=(stageHop A i (Train.top _)).patch; obtain ⟨⟨K,h,hK⟩,_⟩ := sales L x hp'
     change (yen (pullLine L x) q*_).re≤ (yen (pullLine L x) q*_).re
     rw [hK]; simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; exact mul_le_mul_of_nonneg_left (ih _ _ hp') h
lemma soldY (i)(p)(hp:physical p): ∃ y,Tendsto (fun d=> yen ((flying A d i).drive x) (narrow (flying A d i).mass p)) atTop (𝓝 y) :=by
   let z(d:ℕ):= usd A x i d p
   have he d : Silver (z d):= drive_price _ _ _ (narrow_real _ hp)
   have hv : BddBelow (range fun d=>(z d).re):= ⟨0,Set.forall_mem_range.mpr fun d=> (he d).re_nonneg⟩
   have H:= tendsto_atTop_ciInf (antitone_nat_of_succ_le (f:=fun d=>(z d).re) fun d=> swatch A x i d p hp) hv
   exact ⟨_, (Complex.continuous_ofReal.continuousAt.tendsto.comp H).congr fun d=> (he d).of_real⟩
private lemma nozzle_tick (i d): ∃ f : Train (A.clock.J i), (flying A (d+1) i).nozzle=(flying A d i).nozzle ++ [f]:=by
  induction d generalizing i with
  | zero=>exact ⟨Train.top _,rfl⟩
  | succ d ih=>
    obtain ⟨f,hf⟩:= ih (i+1); rw [flight A i (d+1),flight A i d,Flight.land,Flight.land]; simp_rw [Train.nozzle]
    simp only [stageHop,List.cons_append,Flight.patch]; rw [hf,List.map_append]; exact ⟨_,rfl⟩
lemma dusty (i) (p:Momentum)(hp:p∈baseCube): ∃ y:ℂ, 1≤ y.re ∧ Tendsto (fun d=>levelNoise (flying A d i) x p) atTop (𝓝 y):=by
    let f (d:ℕ):= levelNoise (flying A d i) x p
    have hv (d:ℕ): Silver (f d):=by
        suffices ∀ l:List (Train (A.clock.J i)), Silver (stream l x p) from this _
        intro l; induction l with
        | nil=>exact Silver.zero
        | cons v l ih=> exact (feed_cost v x (fun _ _=> Silver.one) _ hp.1).add ih
    have hm : Monotone fun d=>(f d).re:=by
        apply monotone_nat_of_le_succ; intro d
        obtain ⟨v,h⟩:= nozzle_tick A i d; unfold f levelNoise Train.stream; rw [h]; simp only [List.map_append,List.sum_append, List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Complex.add_re]
        exact le_add_of_nonneg_right (feed_cost v x (fun _ _=> Silver.one) _ hp.1).re_nonneg
    obtain ⟨b,C,h,hC,H⟩:=noise_budget (A.clock.adm i) (fun d=> flying A d i) (fun d=> x)
    have hg : BddAbove (Set.range (fun d=>(f d).re)):=⟨C*1,Set.forall_mem_range.mpr fun d=> (Complex.re_le_norm _).trans ((H d).bound p (mem_cube_real (base_subset_realCube h hp) h))⟩
    have H:= tendsto_atTop_ciSup hm hg; have he : f 1 =1:=by
       change feed (.top _) x (fun _=> 1) p+0=1; rw [feed_top,add_zero]
    exact ⟨((⨆ i, (f i).re :ℝ):ℂ), show (1:ℝ)≤⨆ i,(f i).re from by
                    simpa only [he,Complex.one_re] using (le_ciSup hg 1), (Complex.continuous_ofReal.continuousAt.tendsto.comp H).congr fun d=> (hv d).of_real⟩
end YM.Next.Free.OnTrack
