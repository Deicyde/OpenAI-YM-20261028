import YM.TraceExtension.Quince.Pix
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Pieces
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice Wilson RG Pressure Pressure.Tube Precision Labels Source Push Local Planned.PrimaryIntegral295
open Next Next.Foundations Next.Scheduling Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Exterior Bloch JointLoad JointLoad.Heir
open Push.AbsoluteSums Gas Ovens ConnectedActivityE6 Coat Brim Cub Extra.Iteration Extra.Iteration.Scales Malachite
open Place PPX Carrier Next.Free
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open Mallow Pressure.Stores
variable {G:Gauge}{L:Side}{d n:ℕ}{u s t b:ℝ}
section bend
variable (C:Libretto G n)(D:Record) (L p q:ℕ)
lemma garden (L:Side)(p q:ℕ) : ∀ᶠ x:ℝ in atTop, reach x ≤ radiusD x ∧ ∀ (P B:BudgetPoint), P.power=p→ B.power=q → B.threshold=fiery G x L→ P.threshold ≤ 2*B.threshold →
    0≤ loom P (radiusD x) C.C ∧ D.Q*loom P (radiusD x) C.C ≤1∧ loom P (radiusD x) C.C<D.r ∧ B.threshold*(1+(depthW L (radiusD x):ℝ))^B.power ≤ 1:=by
   let w(x:ℝ):= C.C*(2*fiery G x L)*(1+(radiusD x:ℝ))^p
   have hp:Rate G L (-(1/2)) w:=by unfold w; simpa only[add_zero] using ((((Rate.flame (G:=G) (L:=L)).mul_left 2).mul_left C.C).mul (hRate (p:=p)))
   let v(x:ℝ):= (1+(depthW L (radiusD x):ℝ))^q
   have hv:Rate G L 0 v:=by
        have hx: Rate G L 0 (fun x=> (depthW L (radiusD x):ℝ)):=by
             unfold depthW; simp_rw [Nat.cast_mul,show ∀ t:ℕ,((↑(t+2):ℝ))=(t:ℝ)+2 from fun _=>by push_cast;rfl]; exact (((spanDO G L).add (Rate.const 2)).mul_left (L.val:ℝ))
        simpa only[zero_mul] using (((Rate.const 1).add hx).pow q)
   filter_upwards [(Work.E01.radiusB_tendsto).eventually_ge_atTop 100,(hp.mul_left D.Q).below (by norm_num) 1 one_pos, (costzero hp (by norm_num)).eventually (gt_mem_nhds D.radius), ((Rate.flame (G:=G) (L:=L)).mul hv).below (by norm_num) 1 one_pos] with x hx ht hu hw
   constructor
   · unfold Malachite.radiusD Heir.reach; nlinarith
   intro P B hp hv hB hP; let v:=loom P (radiusD x) C.C; have he:0≤v:=by unfold v loom; positivity [P.threshold_pos,C.C_one]
   have hx:v ≤ w x:=by unfold v loom w; rw [← hB,hp]; have hh:=C.C_one; gcongr
   exact ⟨he,(mul_le_mul_of_nonneg_left hx (zero_le_one.trans D.majorant)).trans ((le_abs_self _).trans ht),hx.trans_lt hu,by rw[hB,hv];exact (le_abs_self _).trans hw⟩
end bend
section ally
variable {c f:Side}{S:StepData c f}{y:ℝ}{P B: BudgetPoint}(Y:Support c)(X:Support f){C:Libretto G n}{D:Record}
lemma foliageK (Q:BudgetPoint)(L:Side)(p q:ℕ)(C:Libretto G n)(D:Record) {o:Site f} (hs: X.Nonempty) (hy: S.patch.L=L)(hp : Q.B=radiusB y)(hx : coverNumber Q.B Y ≤ Q.B)(hq:S.ratio.parent o∈Y)
   (h:Heir.reach y ≤ radiusD y)(he:0≤ loom Q (radiusD y) C.C)(hz:D.Q*loom Q (radiusD y) C.C≤1)(ht:loom Q (radiusD y) C.C < D.r)(hh:B.threshold*(1+depthW L (radiusD y) :ℝ)^B.power ≤ 1)(hΩ:1≤ B.B)(hX:∀ v∈X,halo (reach y) {S.ratio.parent v}⊆ Y) : Until C D Q B S o X Y (radiusD y) y ∧ coverNumber B.B X ≤ packing L y :=by
    let m:=radiusD y
    have hq(v:Site c)(he:v∈Y):separation (S.ratio.parent o) v ≤ m:= (Corona.extent Y Q.B hq he).trans (by unfold m radiusD; rw [← hp]; gcongr)
    have hv (i:Site f) (he:i∈X): separation i o ≤ depthW L (radiusD y):=by
       rw[← hy]; exact sep_fore S.ratio i o (by rw [separation_comm]; exact hq _ (hX _ he (halo_subset _ _ (Finset.mem_singleton_self _))))
    refine ⟨⟨he,hz,ht,h,hq,fun j hj=> ?_⟩,?_⟩
    · apply le_trans _ hh; unfold MultiNext.SignedSource.Lyre.width; have hy:= B.threshold_pos; gcongr; exact_mod_cast hv j.1 hj.1
    let w:= depthW L m; have hh: X ⊆ halo (w*B.B) {o}:= fun j hj=> halo_spec.mpr ⟨o,Finset.mem_singleton_self _,by rw [separation_comm]; exact le_trans (hv j hj) (Nat.le_mul_of_pos_right _ hΩ)⟩
    refine (Corona.cover_mono hh B.B).trans ((Corona.tile o w B.B hΩ).trans_eq ?_); unfold packing w m; ring
end ally
end YM.PhysicalNext.Repeat.Quince
