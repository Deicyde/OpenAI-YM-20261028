import YM.UVExtension.Pier.Stock
import YM.UVExtension.Rafter.Pebble
import YM.UVExtension.Copse.Scent
/-! # Pointwise credit, not separate charges for all readings, nor holomorphic
  demands on measurability changes of world coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
open Function Filter Set Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Lotus
open Progress.DirectedRecipe Eyelet Extra.Histories MeasureTheory Push Push.AbsoluteSums
open Lamppost Rafter Copse BoundedContinuousFunction
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {ι D E Z :Type} [NormedAddCommGroup Z][NormedSpace ℂ Z]
    (T: Opening D Z)
variable {a m u b:ℝ}
def Sail (T:Opening D Z)(f:D→ℂ)(a:ℝ):Prop:= ∃ g:Z→ℂ,Bumps T.span g ∧ (∀ i,g (T.call i)=f i) ∧ ∀ z∈ T.span, ‖g z‖≤a
namespace Sail
variable {T}{F X:D→ℂ}
lemma mono (hf:Sail T F a)(hp:a≤b): Sail T F b:=by obtain ⟨g,h,t,v⟩:=hf; exact ⟨g,h,t,fun z hz=> (v z hz).trans hp⟩
lemma plus (hf:Sail T F a)(hg:Sail T X b): Sail T (fun i=> F i+ X i) (a+b):=by obtain ⟨g,h,t,v⟩:=hf; obtain ⟨G,H,K,V⟩:=hg; exact ⟨_, bends_add h H,fun i=>congr_arg₂ (·+·) (t i) (K i),fun z hz=> (norm_add_le ..).trans (add_le_add (v z hz) (V z hz))⟩
lemma scales (hf:Sail T F a)(x:ℂ): Sail T (fun i=>x* F i) (‖x‖*a):=by obtain ⟨g,h,t,v⟩:=hf; exact ⟨fun i=> x*g i,fun s p hs hv ht=> DifferentiableOn.const_mul (h s p hs hv ht) x,fun i=>congr_arg (x*·) (t i),fun z hz=> (norm_mul ..).trans_le (mul_le_mul_of_nonneg_left (v z hz) (norm_nonneg x))⟩
end Sail
variable {G:Gauge}{n:Side}{B:BudgetPoint}
local notation "C"=> Config G n
local notation "ℍ"=> Lab G n
variable (i:Wing)
private theorem liftMark (f:D→ PoleC (G:=G) (n:=n) B i)(b:Z→ℝ)(Y: Z→ C →ℂ)(ht:∀ z∈T.span,∀ U,‖Y z U‖≤b z)(hf:∀ U,Bumps T.span (fun z=> Y z U))(he:∀ d,Y (T.call d) = (f d).val) (hc:∀ z∈T.span,b z ≤ m)(hm:0≤ m):∃ g:Z→ Quoit (grow (G:=G) (n:=n) B i), Bumps T.span g ∧ (∀ d,g (T.call d)=Pin B i (f d))∧∀ z∈ T.span, ‖g z‖ ≤ b z := by
    let v(z): ℍ →ᵇ ℂ:= if h:z∈ T.span then ofNormedAddCommGroupDiscrete (fun d=> Y z d.tag) (b z) (fun d=> ht z h d.tag) else 0
    have hv z (h:z∈ T.span) d: v z d=Y z d.tag:=by unfold v;rw [dif_pos h]; rfl
    have hV z (h:z∈T.span): ‖v z‖≤ b z:= (BoundedContinuousFunction.norm_le ((norm_nonneg _).trans (ht z h 1))).2 (fun i => (hv z h i).symm ▸ ht z h i.tag)
    have heV d:v (T.call d)= (Pin B i (f d)).val:=by
       refine DFunLike.ext _ _ (fun t=>?_); rw [hv _ (T.within d),he]; rfl
    have hY : Bumps T.span v:= canal (M:=m) (fun i s p hs hp hx=> (hf i.tag s p hs hp hx).congr (fun z hz=> hv _ (hp hz) i)) (fun z hz i=> ((v z).norm_coe_le_norm i).trans ((hV z hz).trans (hc z hz))) hm
    have ht(s:Finset D)(p:D→ℂ): ‖∑ j∈s,p j • Pin B i (f j)‖≤ 1*‖∑ j∈s,p j • v (T.call j)‖:=by
      simp_rw [heV,one_mul]; apply le_of_eq
      let L:= (boxes (grow (G:=G) (n:=n) B i)).subtypeL; change ‖_‖= ‖∑j∈s, p j • L (Pin B i (f j))‖; simp_rw [← map_smul,←map_sum]; rfl
    obtain ⟨g,hg,hG,H⟩:=reflectV T (fun d=> Pin B i (f d)) v hY 1 zero_le_one  ht
    exact ⟨g,hg,hG,fun z hz=> (H z hz).trans ((one_mul ‖v z‖).trans_le (hV z hz))⟩

variable (V:D→ Rep G n) {σ v r c e:ℝ} (h:∀ i,(V i).Lawful σ v r c e)
variable (k:ℕ)
-- statement Γ quant all quietly power; measure full cost.P.B
local notation "Γ"=> V

def Harbour (B: BudgetPoint)(V:D→ Rep G n)(a:ℝ):Prop:=∀ (i:Wing),Quiet G n B i → ∀ f:PoleC (G:=G) (n:=n) B i,Sail T (fun d=> hit (V d) i f.val) ((a*worth k B.B B.supportExponent (land G n B i))*‖Pin B i f‖)

variable (F:D → ι → Config G n→ℂ) (Y:ι→Wing)
local notation "P"=> nose (G:=G) (land G n B ∘ Y) k B.B B.supportExponent
include h
lemma traders (he:Harbour T k B V a)(ha:0≤a)(hf:Stalk (P) T F m)(hm:0 ≤ m)(hh:∀ i, Quiet G n B (Y i))(hs:∀ v i,Held B (Y i) (F v i)): Sail T (fun d=> ∑' i, hit (V d) (Y i) (F d i)) (a*m):=by -- jquiet replace
   obtain ⟨N,H,hP,hK⟩:= hf.rises; choose! b hb hT using (fun z hz=> (hK z hz).afloat); let f (i:ι) (d:D): PoleC (G:=G) (n:=n) B (Y i):= ⟨_,hs d i⟩; let p(i):= worth k B.B B.supportExponent (land G n B (Y i))
   have hk z (hz:z∈ T.span): SumBudget (fun i=>p i*b z i) m:= hT z hz (); have hp (i):1≤p i:= Real.one_le_exp (mul_nonneg B.exponent_pos.le (Nat.cast_nonneg _)); have hG (i):∃ g:Z→ℂ,Bumps T.span g∧ (∀ d,g (T.call d)= hit (V d) (Y i) (F d i)) ∧ ∀ z∈ T.span, ‖g z‖ ≤ a*p i*b z i:=by
        let j:= Y i; let W:= PoleC (G:=G) (n:=n) B j; let ψ:= grow (G:=G) (n:=n) B j; let w:=Pin (G:=G) (n:=n) B j
        have hW:DenseRange w:= steams ψ; let ℓ(d:D):= tariff B j (V d) (h d); let x:= a*p i
        have hG d t: ‖ℓ d t‖≤ x*‖w t‖:=by obtain ⟨g,hg,hQ,h⟩:= he j (hh i) t; specialize h (T.call d) (T.within d); rw [hQ] at h; exact h
        let L(d:D): Quoit ψ →L[ℂ]ℂ:= (ℓ d).extendOfNorm w; have hL(d:D)(v:W): L d (w v)= hit (V d) j v.val:= LinearMap.extendOfNorm_eq hW ⟨x,hG d⟩ _
        have he' (v:W): Sail T (fun d=> L d (w v)) (x*‖w v‖):=by simp_rw [hL]; exact he j (hh i) v
        obtain ⟨g,hg,hQ,hg'⟩:= Rafter.flick T L w hW (mul_nonneg ha (zero_le_one.trans (hp i))) he'
        have ht(z)(hz:z∈ T.span):b z i ≤ m := (le_mul_of_one_le_left (hb z hz i|>.1) (hp i)).trans (budget_single (hk z hz) i)
        obtain ⟨q,hq,hv,hq'⟩:=liftMark T j (f i) (fun z=>b z i) (fun z=>N z i) (fun z hz U=> (hb z hz i).2 U) (H i) (fun d=> congr_fun (hP d) i) ht hm
        refine ⟨fun z=>g z (q z),fun s p hs hh he=> DifferentiableOn.clm_apply (hg s p hs hh he) (hq s p hs hh he),fun d=> ?_,fun z hz=>?_⟩
        · dsimp only; rw [hQ,hv]; exact hL d (f i d)
        exact ((g z).le_opNorm _).trans (mul_le_mul (hg' z hz) (hq' z hz) (norm_nonneg _) (mul_nonneg ha (zero_le_one.trans (hp i))))
   choose g hg hE hQ using hG
   have hp(z)(hz:z∈T.span): SumBudget (fun i=>‖g i z‖) (a*m):= Local.sumBudget_mono (Local.sumBudget_mul_left (hk z hz) ha) (fun _=>norm_nonneg _) (fun i=> (hQ i z hz).trans_eq (mul_assoc ..)) le_rfl
   exact ⟨_, Rafter.washed g hg hp (mul_nonneg ha hm),fun d=> tsum_congr (fun i=> hE i d),fun z hz=> (norm_tsum_le_tsum_norm (hp z hz).2.1).trans (hp z hz).2.2⟩
omit h
lemma accounted (hf:Stalk (P) T F m)(d:D): Dominated (F d):=by
   obtain ⟨g,hg,hP,hV⟩:= hf.rises; let e:=T.call d; obtain ⟨b,hb,he⟩:= (hV _ (T.within d)).afloat
   have hh := he (); have hp i:1≤ (P).cost () i:= Real.one_le_exp (mul_nonneg B.exponent_pos.le (Nat.cast_nonneg _))
   rw [← hP]; exact ⟨b,Summable.of_nonneg_of_le (fun i=>hb i|>.1) (fun i=> le_mul_of_one_le_left (hb i|>.1) (hp i)) hh.2.1,fun i x=> (hb i).2 x⟩
end YM.UVExtension.Pier
