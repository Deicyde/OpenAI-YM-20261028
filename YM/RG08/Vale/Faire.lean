import YM.RG08.Vale.Pit
/-!
# Simultaneous polynomial wallets, in unbounded polynomial directions
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {p m c: Side} {D d e j r n i k:ℕ}
lemma coins_wrap (x:Cover)(n:ℕ)(m:Side): dime n (lift (wrap m x)) ≤ dime n x := by unfold dime Carrier.liftCost; gcongr; exact FreeResolvent.wrap_size ..
lemma coin_step (n:ℕ): ∃ A:ℝ,0≤A ∧ ∀ i : Axis,∀ x:Cover, dime n (x+step i) ≤ A*dime n x := by
  let A:=∑ i:Axis,dime n (step i); have he : ∀ i:Axis, 0≤dime n (step i) := fun i=> Carrier.liftCost_pos n _
  refine ⟨A,sum_nonneg fun i _=> he i,fun i x=>?_⟩; rw [mul_comm]; exact (Carrier.liftCost_add ..).trans (mul_le_mul_of_nonneg_left (single_le_sum (fun i _=>he i) (mem_univ i)) (Carrier.liftCost_pos ..))

variable (X:Fin r→ Snap G d) (W:Fin r→ E4→G.Color)
lemma ped_pile (h : ∀ i, W i ∈ Place.rangeLt G.Color n) (x:Stage r): ∃ C:ℝ,0≤C ∧ ∀ a, ‖pedestal W a x‖ ≤ C*dime n a := by
  let b : Place.Potential G := fun y _=> ∑ i,x i • W i y
  have hb : b ∈ Place.rangeLt (Axis →G.Color) n := by
    apply vector_band; intro i
    apply Eq.subst (_ : (∑ i,x i • W i)=(fun y=> b y i)) (Submodule.sum_mem _ (fun i _=> Submodule.smul_mem _ (x i) (h i))) -- change
    ext1 y; unfold b; rw [Finset.sum_apply]; rfl
  obtain ⟨C,hc,he⟩:= Carrier.royalties n b hb
  exact ⟨C,hc,fun i=>by rw [pedestal,rung_at]; exact he i 0⟩
lemma seam_fee (h : ∀ i, W i ∈ Place.rangeLt G.Color n)(hp:d≤n)(x:Stage r) : ∃ C:ℝ,0≤C ∧ ∀ (y:Cover)(a:Axis)(m:Side),
    ‖seam X W m (wrap m y) a x‖ ≤ C*dime n y := by
  obtain ⟨A,hA,hE⟩:=ped_pile W h x; obtain ⟨B,hB,hW⟩:= coin_step n
  let R:=‖rung X x‖
  have hR : 0≤R := norm_nonneg (rung X x)
  refine ⟨A+A*B+R,by positivity,fun y a m=>?_⟩
  let z:=wrap m y; have ht:=hE (lift z); have hf:=hE (lift (z+step a)); let f:=dime n y; have he : 0 ≤ f := Carrier.liftCost_pos ..
  have hx:= coins_wrap y n m
  have hv : ‖pedestal W (lift z) x‖≤ A*f:= ht.trans (mul_le_mul_of_nonneg_left hx hA)
  have hh : ‖pedestal W (lift (z+step a)) x‖ ≤ A*B*f := by
    apply hf.trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hA; unfold z
    rw [← show wrap m (y+step a)=wrap m y+step a from by rw [map_add,wrap_step]] -- maybe simp
    exact (coins_wrap (y+step a) n m).trans (hW a y)
  have hV : ‖Place.road (Place.seat (lift z)) a (rung X x)‖ ≤ R*f := by
    calc
      _ ≤ ‖Place.road (Place.seat (lift z)) a (G:=G) (d:=d)‖* R := (Place.road (Place.seat (lift z)) a (G:=G) (d:=d)).le_opNorm _
      _ ≤ f*R := mul_le_mul_of_nonneg_right ((Film.road_cap ..).trans ((dime_more hp _).trans hx)) hR
      _ = _ := mul_comm ..
  have hP := (norm_sub_le (pedestal W (lift z) x) (pedestal W (lift (z+step a)) x)).trans (add_le_add hv hh)
  change ‖(pedestal W (lift z) x, pedestal W (lift z) x - pedestal W (lift (z+step a)) x,Place.road (Place.seat (lift z)) a (rung X x))‖ ≤ (A+A*B+R)*f
  rw [Prod.norm_def,Prod.norm_def,max_le_iff,max_le_iff,add_mul,add_mul]
  have hb : 0≤A*B*f:= by positivity
  have hu :0≤ A*f:= by positivity
  have ht' : 0≤R*f:= by positivity
  exact ⟨by linarith only [hb,hv,ht'],by linarith only [hP,ht'],by linarith only [hV,hb,hu]⟩
lemma theater (h : ∀ i, W i ∈ Place.rangeLt G.Color n) (hb:d≤n): Plenty (floorP X W) boards (fun m=>curtain X W (boards m)) := by
  intro j x; constructor
  · intro p; let i:= (heap p).2
    refine EventuallyEq.tendsto ?_; filter_upwards [Next.Free.eventually_unfold boards board_end p.1,Next.Free.eventually_unfold boards board_end (p.1+step i)] with a ha hh
    let m:= boards a; have hv : lift (wrap m p.1+step i)=p.1+step i := by
      have hz: wrap m (p.1+step i)=wrap m p.1+step i := by rw [map_add, wrap_step]
      rw [← hz]; exact hh
    rw [curtain_card]
    change scent _ (iteratedFDeriv ℝ j Place.logo _ ((seam X W m (wrap m p.1) i) ∘ x))= _; unfold seam; rw [hv,show lift (wrap m p.1)=p.1 from ha]
    exact (motionD ..).symm
  choose C hC H using fun i=> seam_fee X W h hb (x i)
  let M:= iteratedFDeriv ℝ j (Place.logo (G:=G) (d:=d)) 0
  have hM : 0≤ ‖M‖:= norm_nonneg M
  refine ⟨n*j,‖M‖*∏ i,C i, mul_nonneg hM (prod_nonneg fun i _=> hC i),fun p a=> ?_⟩
  let L:= seam X W (boards a) (wrap (boards a) p.1) (heap p).2; let q := L ∘ x
  calc
    _ = ‖scent p.2.2 (M q)‖ := congr_arg (fun x:ℝ=>‖x‖) (curtain_card ..)
    _ ≤ ‖M q‖:= PiLp.norm_apply_le (M q) _
    _ ≤ ‖M‖*∏ i, ‖q i‖:= M.le_opNorm _
    _ ≤ ‖M‖*∏ i,(C i*dime n p.1) := mul_le_mul_of_nonneg_left (prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> H i _ _ _)) hM
    _ = _:= by simp [prod_mul_distrib, dime,Carrier.liftCost,pow_mul, mul_assoc]
end YM.RG08.Vale
