import YM.UVExtension.Projection.Chord

/-! Unique licensed path arrays from heading jet and modulo-decaying driver. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Lattice RG Precision Tree Exterior Bloch Laurent Wilson Stationary Filter Function Finset
open scoped Matrix Topology BigOperators ContDiff Classical
variable {G : Gauge} (P : Rates G) (Y : Bed)

abbrev Head (P : Rates G) := (i : ℕ)→ (n : Fin 5)→ (Fin n → Link G (P.stageSide i)) → ℝ
abbrev Stamp (P : Rates G) := (i : ℕ) → (Fin 2→ Link G (P.stageSide i)) → ℝ

def reading (B : Bed):Stamp P := fun _ v=> Bid.gaugeFiscal B (arm _ _ _ (v 0)) (arm _ _ _ (v 1))

def style (h : ∀ i, Link G (P.stageSide i)→ℝ):Stamp P:= fun i v=> iteratedFDeriv ℝ 2 (h i) 0 v
structure Keyline (B : Bed) : Prop where
    scale : ∃ s C, 0<s ∧ B.metric.strip s C
    tap : B.metric.read 0=1
    sym i (x y:Link G (P.stageSide i)): reading P B i ![x,y]=reading P B i ![y,x]

theorem Keyline.blue {B} (h : Keyline P B): ∃ f:∀ i, Link G (P.stageSide i)→ℝ,(∀ i, AnalyticAt ℝ (f i) 0) ∧ style P f=reading P B∧ ∀ i,Recorded (slots B.metric G) (f i) 0:=by
  have hx (i:ℕ): ∃ f: Link G (P.stageSide i)→ℝ,AnalyticAt ℝ f 0 ∧ (∀ v:Fin 2→ Link G (P.stageSide i),iteratedFDeriv ℝ 2 f 0 v=reading P B i v) ∧ Recorded (slots B.metric G) f 0:=by
    let m:=P.stageSide i; let W (x y: Link G m):= reading P B i ![x,y]; let q:=K (B.metric.acts m)
    have he (x y:Link G m):W x y = ∑ i, parts G 1 (arm G m 1 x) i ⬝ᵥ (q *ᵥ parts G 1 (arm _ _ _ y) i) := rfl
    let g : Link G m→ℝ:= fun x=>W x x/2
    have hf : AnalyticAt ℝ g 0:= by
      apply (show ContDiff ℝ ω g from ?_).contDiffAt.analyticAt
      unfold g; simp_rw [he]; apply ContDiff.div_const; apply ContDiff.sum; intro j _; unfold parts Matrix.mulVec dotProduct; refine ContDiff.sum fun i _=> ContDiff.mul ?_ (ContDiff.sum fun k _=> contDiff_const.mul ?_)
      · exact contDiff_apply ℝ ℝ (i.1,i.2,j)
      exact contDiff_apply ℝ ℝ (k.1,k.2,j)
    have ha : ∀ x y,iteratedFDeriv ℝ 2 g 0 ![x,y]=W x y:=by
      refine (Work.F03.hessian_of_limit hf.contDiffAt (fun x=>?_ ) (fun x y z=> ?_) (h.sym i)).2.2
      · have hv (t:ℝ): g (t • x)=t^2 *W x x/2:= by
          unfold g W reading Bid.gaugeFiscal; simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_smul]
          have hk (i:G.ColorIndex)(z:fieldDir G m 1):parts G 1 (t • z) i=t • parts G 1 z i:=rfl
          simp_rw [hk,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]; simp [sq, mul_assoc, Finset.mul_sum]
        apply tendsto_const_nhds.congr' -- t²
        filter_upwards [(self_mem_nhdsWithin : ∀ᶠ u : ℝ in cutRay,u≠0)] with t ht
        change t≠0 at ht
        change W x x / 2=g (t • x) / t^2; rw [hv]; field_simp
      · simp [W,reading,Work.F03.gaugeFiscal_add]
    obtain ⟨s,C,hs,hC⟩:=h.scale
    refine ⟨g,hf,fun v=>?_,according (B.metric.rights s C hC hs.le) ha⟩
    rw [show v=![v 0,v 1] from funext fun i=> by fin_cases i <;> rfl]; exact ha _ _
  choose f hf hF H using hx
  exact ⟨f,hf,funext fun i=> funext fun v=> hF i v,H⟩

structure Toned (P : Rates G):Prop where
    climb : Tendsto (fun i=> (P.stageSide i).val) atTop atTop
    echo (x : Cube G) : x∈ P.valid → ∃ K : Picture G 1, ∃ s C,0<s ∧ (∀ i, AnalyticAt ℝ (P.eHat x i) 0 ∧ Recorded K (P.eHat x i) 0) ∧ ∀ i j,Firm s C (K i j) ∧ Rays 4 (K i j ∘ axes)

def stroke (x:Cube G): Head P:= fun i j v=> iteratedFDeriv ℝ j (P.hat x i) 0 v
def quick (x:Cube G): Stamp P:= style P (P.eHat x)
def priceLoop (B : Bed)(r:Cube G × ℝ): Stamp P := r.2 • reading P B + quick P r.1

def Neglect (f:Stamp P):=∃ b:ℕ→ℝ,Tendsto b atTop (𝓝 0)∧∀ i (p q : Site (P.stageSide i)) (x y: HatWave G), ValidPitch x → ValidPitch y→ ‖f i ![pew p x,pew q y]‖ ≤ cents (P.stageSide i)* b i
lemma annihilate (i : G.ColorIndex)(h:Toned P) (B : Bed)(hp:Keyline P B)(x:Cube G)(a:ℝ)(he : P.Lodge x)(hg: stroke P x=0)(hr:Neglect P (priceLoop P B (x,a))): x=0 ∧ a=0:=by
  obtain ⟨b,hb,hB⟩:=hr; obtain ⟨f,hf,hF,H⟩:=hp.blue P; obtain ⟨K,v,D,hv,hK,hG⟩:=h.echo x he.2
  let s j:= a • f j+P.eHat x j; let M:=(a:ℂ) • slots B.metric G+K
  have hz j: AnalyticAt ℝ (a • f j) 0:= analyticAt_const.mul (hf j)
  have ht j: Recorded M (s j) 0:= Recorded.both (hz _) (hK j).1 ((H j).weigh a (hf _)) (hK j).2
  have hR j p: iteratedFDeriv ℝ 2 (s j) 0 p= priceLoop P B (x,a) j p:=by
    unfold s; rw [iteratedFDeriv_add_apply (hz j).contDiffAt (hK j).1.contDiffAt,iteratedFDeriv_const_smul_apply (hf j).contDiffAt]; unfold priceLoop; rw [← hF]; rfl
  obtain ⟨w,C,hw,hC⟩:=hp.scale
  let z:= min w v; have hZ : 0<z:=lt_min hw hv
  have hE k: Recorded 0 (s k) (cents (P.stageSide k)*(4*b k)) (t:=1):=by
    rw [mul_left_comm]; refine rhyme (fun p q u v he hp=>?_); rw [hR]; exact hB k _ _ _ _ he hp
  have hP i j: Firm z (‖(a:ℂ)‖ * bedCharge w C+D) (M i j):= ((Firm.const (α:=Keys 1) hZ (a:ℂ)).mul ((slots_cost hw hC i j).mono hZ (min_le_left ..) le_rfl)).add ((hG i j).1.mono hZ (min_le_right ..) le_rfl)
  obtain ⟨hx,hl⟩:=hear_price s M h.climb (fun i=>4*b i) (by simpa using hb.const_mul 4) hZ hP ht hE
  let F:= pressLens (slots B.metric G) ![i,i] 1 1
  let L:= pressLens K ![i,i] 1 1
  have hL : a • F= -L:=by
    ext1 p
    have hz := hx ![i,i] ![coord 1,coord 1] (roads p)
    apply eq_neg_of_add_eq_zero_left (b:= L p) ?_; unfold L F pressLens; simpa [Complex.real_smul,M] using hz
  have ha : a=0:=by
    let r:Track:=step (0:Axis); have hi: speedy F 2 r=(1/2:ℂ):=tip_fuel i hC hw hp.tap
    have he:AnalyticAt ℝ F 0:=priceL (slots_cost hw hC) ..
    have hY:Rays 3 L :=by
      intro r; unfold L pressLens; simp_rw [map_smul]; exact ((hG _ _).2.weaker (by decide)) (roads r)
    have hD:AnalyticAt ℝ L 0:=priceL (fun i j=> (hG i j).1) ..
    have hm : iteratedFDeriv ℝ 2 L 0=0:= (rays_jet hD _).mp hY _ (by decide)
    have hd : a • speedy F 2 r=0 := by
      rw [show a • speedy F 2 r=speedy (a • F) 2 r from ?_, hL]; unfold speedy Tensor.coeff; rw [iteratedFDeriv_neg_apply,hm,neg_zero,smul_zero]; rfl
      unfold speedy Tensor.diagonal Tensor.coeff; rw [iteratedFDeriv_const_smul_apply he.contDiffAt,_root_.smul_apply,_root_.smul_apply,_root_.smul_apply]; exact smul_comm ..
    rw [hi] at hd; exact (smul_eq_zero.mp hd).resolve_right (by norm_num)
  subst a
  have hz : x∈P.seam:= by
    refine ⟨he.2,fun i=> ⟨fun j hj v=> congr_fun (congr_fun (congr_fun hg i) (⟨j,by omega⟩: Fin 5)) v, fun v=>?_⟩⟩
    have hx:=hl i; simp only [s,zero_smul,zero_add] at hx; rw [hx]; rfl
  exact ⟨(Submodule.mem_bot ℝ).mp (P.seam.inf_orthogonal_eq_bot ▸ (show x∈P.seam⊓P.seamᗮ from ⟨hz,he.1⟩)),rfl⟩
end YM.UVExtension.Projection
