import YM.TraceExtension.Pi.Lith
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory Source Source.Drops Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin StressFlux Labels
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge} (d i b:Axis)(a:G.ColorIndex)
open Complex
-- sign factors in Helicity under polar signed transform
abbrev sFlag (S:Signed)(x:Axis):ℤ:= if S.flip x then -1 else 1
lemma signUp (S:Signed)(p:Axis)(x:ℤ): S.act (ra p x)= ra (S.perm p) (sFlag S p*x):=by ext1 i; obtain ⟨i,rfl⟩:=S.perm.surjective i; rw[S.act_at]; unfold sFlag; by_cases he:i=p <;> cases hz:S.flip p <;> simp[ra,he, *,apply_ite]
lemma signDown (S:Signed)(p:Dish): let z:= (sFlag S d*p.1,sFlag S b*p.2); lawn (S.perm d) (S.perm b) z = fun i=> S.act (lawn d b p i):=by
   intro z; funext i; rw[reeling,reeling]; fin_cases i
   · change reel _ =S.act (reel _); rw [← turn_mask]; unfold z; rw [signUp]
   change reel _= S.act (reel _); rw[← turn_mask]; unfold z reab;rw [Signed.act_add,Signed.act_neg,signUp,signUp]
lemma sign_deb (F:Dish→ℂ)(S:Signed): Deb (fun v=> F (sFlag S d*v.1,sFlag S b*v.2))=(sign S b:ℂ)*Deb F :=by
   change Complex.I * PanZ _=_*(Complex.I*PanZ _); unfold sFlag sign; split_ifs<;>simp only[pani,flopi]<;> norm_num<;> ring
lemma clamp (S:Signed)(p:Label G 5)(hp:G.Simple): lag (S.perm d) (S.perm i) (S.perm b) a (sign S b • tensor S.ortho p)=lag d i b a p:=by
    let v:= sign S b; have hv:v^2=1:= sign_sq S b; let L(x):= lotR (S.perm i) a (lawn (S.perm d) (S.perm b) x) (tensor S.ortho p)
    have h(x:Dish): L (sFlag S d*x.1,sFlag S b*x.2)= lotR i a (lawn d b x) p:=by unfold L; rw [signDown d b]; unfold lotR; simp only[LinearMap.smul_apply,LinearMap.add_apply, roseR i a S _ _ p hp]
    have hc: sign S b • Deb L=( (sign S b:ℝ):ℂ)*Deb L:=rfl
    change ((lag (S.perm d) (S.perm i) (S.perm b) a).restrictScalars ℝ) _=Deb (fun x=>lotR i a (lawn d b x) p); rw[map_smul]; change v • Deb L=_; rw[← funext h,sign_deb d b]; exact hc
lemma coin_r (S:Signed)(p q:Axis→Label G 5)(h:G.Simple)(hp:∀ i,q (S.perm i)=sign S i • tensor S.ortho (p i)): archK a q= archK a p:=by
    rw [arch_pay,arch_pay]; unfold suite; rw [← Equiv.sum_comp S.perm]; refine sum_congr rfl fun d _=>?_ ; rw [← Equiv.sum_comp S.perm]; apply sum_congr rfl fun i _=>?_; simp only [S.perm.injective.eq_iff]; by_cases he:d=i <;> simp only[he,↓reduceIte]
    rw [← Equiv.sum_comp S.perm]; exact sum_congr rfl fun b _=> by rw[hp b]; exact clamp d i b a S (p b) h
end YM.Trace.Kits
