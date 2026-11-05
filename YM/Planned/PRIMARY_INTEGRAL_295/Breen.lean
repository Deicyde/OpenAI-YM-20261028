import YM.Planned.PRIMARY_INTEGRAL_295.Drupes
import YM.Planned.PRIMARY_INTEGRAL_295.Flutes
/-!
# Branch-independent analytic core linear kernel path allowances

Including labelled cover arithmetic (no period-limited index charges),
windings and signed journeys. Post-L cost for True D/F0 pre-template. Same
b real marginal. No rotor covariance approximation. Doesn't sum Fro gas input
per site. No assumptions all rows beyond Spec. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Breen
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Laurent Place
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bunks Little Work.F01 Little.Core Push.Uniform  Drupes Density  
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Gauge} {k R d : ℕ} {c s f : Side} {S:StepData c f}

section
lemma steps (x y:Cover): (route x y 1).length=size (y-x):= by
   have ha : allAxes 1 = [0,1,2,3]:= by decide
   simp [route,axisRoute,ha,size,Fin.sum_univ_succ,straight,Axis]
lemma seized (x:Cover)(d:ℕ):size (d • x)=d*size x:=by simp [size,Pi.smul_apply,Int.natAbs_mul,Finset.mul_sum]
lemma maxlift (L:Side)(x:Site L):size (lift x) ≤ 4*L.val:=by
    unfold size; apply le_trans (Finset.sum_le_sum (g:=fun _=> L.val) (fun i _=>?_));
    · simp [Axis]
    have hh:=lift_centers x i; omega

-- Finite ferry estimates. Supplier all sizes.
section Carter
variable [Fintype Y] {β:Type} [Fintype β]

/-- Packed with physical range R on lengths, never declares rows no journey longer than lattice stencil.
E.g. µ leaps on connector paths. `y`: projection Space, `W`: starting site reading on W actual.
`x` chart input y, `q`: one parameter. -/
def line (u:Site c)(a:Site f) (p:Y≃ Co c β) (K:β→ Cover→ℝ)(r:Cover→Walk) (d R:ℕ)
    (U:Config G f) (y:Y)(x:Cover): Pay G:=
   if (r x).length*d ≤ R ∧ (p y).1=u+wrap c x then rated U a (r x) (K (p y).2 x) else 0

-- support version explicitly post-L charger. proposals distinct.
lemma network (G:Gauge)(β:Type) [Fintype β] (k:ℕ) (C η A H:ℝ) (hc:0≤C)(he:0<η)(ha:0≤A)(hh:0<H) :∃ M:ℝ,1≤M∧
   ∀ {E Y:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype Y] {c f:Side}(u:Site c)(a:Site f) (p:Y ≃ Co c β)
    (K:β→Cover→ℝ)(_:∀ i,Laurent.Width η A (K i))(r:Cover→Walk)(d R:ℕ) (_:0<d) (_:∀ x:Cover,((r x).length:ℝ) ≤ H*(1+size x))
    (_:∃ S:Finset Cover,∀x:Cover,(r x).length*d ≤ R → x∈ S)(U:E→Config G f)(x:E) (_:∀ i, Allows k (fun y=>G.mat (U y i)) x C),
    ∃ B:Y→ℝ,(∑ y,B y)≤M ∧ ∀ i,Allows k (fun y=> ∑' z,line u a p K r d R (U y) i z) x (B i) := by
   let τ := η/H; have ht :0<τ:= by unfold τ; positivity
   obtain ⟨D,hD,hF⟩:= enroll_speed C hc G k τ ht; let P:= D*Real.exp η; let L:= P*((Fintype.card β:ℝ)*A)
   have hp :0≤P:=by unfold P; positivity
   refine ⟨1+L,le_add_of_nonneg_right (by unfold L; positivity),?_⟩
   intro E Y _ _ _ c f u a p K hk r d R hd hw ⟨S,hS⟩ U x h
   let g i (z:Cover):= Real.exp (η*size z)*‖K i z‖
   let m i z := if (p i).1 = u+wrap c z then g (p i).2 z else 0
   let v (i:Y):= ∑ z∈S, P*m i z
   refine ⟨v,?_,fun y=> ?_⟩
   · unfold v; simp_rw [←Finset.mul_sum]; rw [Finset.sum_comm]; apply le_trans (b:=L) ?_ (le_add_of_nonneg_left zero_le_one)
     apply mul_le_mul_of_nonneg_left _ hp; simp_rw [← p.symm.sum_comp (fun y=> m y _),Fintype.sum_prod_type, m, Equiv.apply_symm_apply];
     conv_lhs => arg 2; intro z; rw [Finset.sum_comm]
     have hg i :∑ z∈S,g i z ≤ A:= (Summable.sum_le_tsum S (fun z _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (hk i).2.1).trans (hk i).2.2
     simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]; rw [Finset.sum_comm]
     exact (Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hg i)).trans_eq (by simp)
   have hy(w:E): (∑' z,line u a p K r d R (U w) y z)=∑ z∈S,line u a p K r d R (U w) y z := by
      apply tsum_eq_sum; intro z hz; unfold line; split_ifs with H; exacts [False.elim (hz (hS _ H.1)),rfl]
   simp_rw [hy]; apply Push.Uniform.allows_sum; intro i hi
   simp only [line,m];
   by_cases hx:(p y).1=u+wrap c i
   swap; · simp only [hx,and_false,if_false,mul_zero]; exact allows_const x (by simp)
   simp only [hx,and_true,if_true]; split_ifs with hy
   · apply ((hF h a (r i)).smul (K (p y).2 i)).mono; let v:=K (p y).2 i
     have he: Real.exp (τ*(r i).length)≤Real.exp η*Real.exp (η*size i):=by
         rw [←Real.exp_add]; apply Real.exp_monotone
         apply (mul_le_mul_of_nonneg_left (hw i) ht.le).trans_eq; unfold τ; field_simp
     calc
       |v| * (D*Real.exp (τ*(r i).length)) ≤ |v| * (D*(Real.exp η*Real.exp (η*↑(size i)))):=by gcongr
       _ = _:= by change _=D*Real.exp η*(Real.exp (η*↑(size i))*‖v‖); rw [Real.norm_eq_abs]; ring
   apply allows_const x; rw [norm_zero]; unfold g; positivity
end Carter

section Doms
variable (G:Gauge)(k:ℕ) (P:Patch)(η C H:ℝ)(hη:0<η)(hC:0≤C)(hH:0≤H)
include hη hC hH

lemma pencils:∃ M:ℝ,1≤M∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{c f:Side}(S:StepData c f)(K:Core G S),S.patch=P→
   K.tube.R.mn.strip η H →∀ (U:E→Config G c)(p:Bond c) (x:E) (_:∀ i,Allows k (fun y=>G.mat (U y i)) x C),
   ∃ B:Twin c→ℝ,(∑ y, B y)≤M ∧ ∀ i,Allows k (fun y=>K.tube.Φ' K.R (U y) p i) x (B i):=by
   obtain ⟨M,hM,h⟩:= network G Layers2 k C η H 1 hC hη hH one_pos
   refine ⟨M,hM,?_⟩
   intro E _ _ c f S K ht hp U p x hU
   let P:=Work.E03.meshEquiv c; let d:=S.patch.L.val
   let r(x:Cover):=route 0 x 1; let F:=K.tube.R.mn; let W:=F (coord p.2)
   have he(x:Cover):(r x).length= size x:=by unfold r; rw [steps,sub_zero]
   obtain ⟨B,hB,hk⟩:=h p.1 p.1 P W (hp (coord p.2)) r d K.R S.patch.L.property
      (fun x=>by rw [he x,one_mul]; linarith) ⟨box K.R,fun x hx=> by rw [he x] at hx; exact Racks.within ((le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property).trans hx) (Flutes.stems x)⟩ U x hU
   · exact ⟨B,hB,hk⟩

lemma resumes:∃ M:ℝ,1≤M∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{c f:Side}(S:StepData c f)(K:Core G S), S.patch=P → K.tube.R.mf.strip η H →
    ∀ (U:E→Config G c)(p:Twin f)(x:E) (_:∀ i, Allows k (fun y=> G.mat (replica S.ratio (U y) i)) x C),
    ∃ B:Twin c→ℝ,(∑ y,B y)≤ M ∧ ∀ i,Allows k (fun y=>K.tube.Φ K.R (U y) p i) x (B i):=by
    have hp:0 < (P.L.val:ℝ):=by exact_mod_cast P.L.property
    obtain ⟨M,hM,h⟩:=network G Layers2 k C η H (4*P.L.val) hC hη hH (by positivity)
    refine ⟨M,hM,?_⟩
    intro E _ _ c f S K ht hv U p x hU
    let P':=S.patch; let V:=Work.E03.meshEquiv c; let d:= S.patch.L.val; let t:Site f:=(mesh p).1
    let z:= Lattice.lift (S.ratio.residue t); let r(x:Cover):=route z (d • x) 1
    let F:=K.tube.R.mf; let W:=F (S.ratio.residue t,(mesh p).2)
    obtain ⟨rfl⟩:=ht
    have he(x:Cover):(r x).length=size (d • x-z):= steps ..
    have hh:size z ≤4*d:=maxlift ..
    have hw (x:Cover):(r x).length≤4*d*(1+size x):=by
       rw [he,sub_eq_add_neg]; apply (size_add ..).trans; rw [size_neg,seized]; nlinarith
    have hR (x:Cover): (r x).length ≤ K.R→ size x≤ K.R +4*d:=by
       rw [he]; intro hs; apply le_trans (le_mul_of_one_le_left (Nat.zero_le _) (S.patch.L.property)); rw [←seized x]
       apply le_trans (b:=size (d • x-z) + size z) _ (add_le_add hs hh)
       change size (d • x) ≤ _; simpa only [sub_add_cancel] using size_add (d•x-z) z
    obtain ⟨B,hB,hk⟩:=h (S.ratio.parent t) t V W (hv _) r 1 K.R one_pos (fun i=>by exact_mod_cast hw i)
       ⟨box (K.R+4*d),fun x hx=> Racks.within (hR _ (by rwa [mul_one] at hx)) (Flutes.stems x)⟩ (fun x=>replica S.ratio (U x)) x hU
    refine ⟨B,hB,fun i=> (hk i).germ ?_⟩
    refine Eventually.of_forall fun y=> tsum_congr fun z=>?_
    unfold line; rw [mul_one]; rfl
end Doms
end
end YM.Planned.PrimaryIntegral295.Breen
