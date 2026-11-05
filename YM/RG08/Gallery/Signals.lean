import YM.RG08.Gallery.Script

/-!
# Sparse unveneered first field-rank departure. Determine by total law at g, even if
 other (field-independent) grades are unknown.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Gallery
open Forms Glyph Room Camera Finset Lattice Laurent Pert.Bulk Function MvPolynomial Filter Isles
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {I J : Type}{n k:ℕ}

-- sparse field positions selected by their tester, on naked constant fields.
structure Demo (I:Type) where
 firm:Finset I
 play:I→ℝ
 size' :∀ i∉firm,play i=0
namespace Demo
def flat (a:Tray I):Demo I:=⟨a.base,fun i=> PowerSeries.constantCoeff (a.get i),fun i hi=>by rw [a.shut i hi,map_zero]⟩
def pump (a:Demo I):Tray I:=⟨a.firm,fun i=>PowerSeries.C (a.play i),fun i hi=>by rw [a.size' i hi,map_zero]⟩
def add (a b:Demo I):Demo I:=⟨a.firm∪b.firm,a.play+b.play,fun i hi=>by
  have H:i∉a.firm∧i∉b.firm:=by simpa using hi
  rw [Pi.add_apply,a.size' _ H.1,b.size' _ H.2,add_zero]⟩
def reals (z:ℝ)(a:Demo I):Demo I:=⟨a.firm,z • a.play,fun i hi=>by simp [a.size' _ hi]⟩
end Demo
variable {F:Flake n I}
def basic (a:Demo I)(x:Tape n I):ℝ:=∏ i,a.play (x i)
def regard (F:Flake n I)(a:Demo I):ℝ:=∑ x∈desks a.firm n,F x * basic a x
lemma basic_zero (a:Demo I)(x:Tape n I)(h:x∉desks a.firm n):basic a x=0:=by
 have he:¬∀ i,x i∈a.firm:=by simpa [desks] using h
 obtain ⟨i,hi⟩:=Classical.not_forall.mp he
 exact Finset.prod_eq_zero (mem_univ i) (a.size' _ hi)
lemma regard_price (F:Flake n I)(a:Demo I){s:Finset I}(h:a.firm⊆s):regard F a=∑ x∈desks s n,F x*basic a x:=
 Finset.sum_subset (show desks a.firm n⊆desks s n from fun x hx=>by simp only [desks,Fintype.mem_piFinset] at *;exact fun j=>h (hx j)) (fun y hy hY=>by rw [basic_zero _ _ hY,mul_zero])
lemma regarded (a:Demo I): tap 0 (volume F (Demo.pump a))=regard F a:=by simp [volume,Demo.pump,regard,tap,fret,basic]
lemma regard_at (a:Tray I): tap 0 (volume F a)=regard F (Demo.flat a):=by simp [tap,fret,volume,Demo.flat,basic,regard]
lemma regard_eq {a b:Demo I}(h:a.play=b.play):regard F a=regard F b:=by rw [regard_price F a (s:=a.firm∪b.firm) Finset.subset_union_left,regard_price F b (s:=a.firm∪b.firm) Finset.subset_union_right];simp only [basic,h]
lemma regard_slug (F:Flake n I){a b:Demo I}{z:ℝ}(h:a.play=z • b.play):regard F a=z^n *regard F b:=by rw [regard_price F a (s:=a.firm∪b.firm) Finset.subset_union_left,regard_price F b (s:=a.firm∪b.firm) Finset.subset_union_right];simp only [basic,h,Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.mul_sum];simp_rw [mul_left_comm]

lemma detour {V:Script I}{e:ℕ}(s t:Tray I)(h:∀ k<e,∀ i≠0,V k i=0) (hh: tap e (announced V s)=tap e (announced V t)):
 (∑ i∈range (e+3),regard (V e i) (Demo.flat s))= (∑ i∈range (e+3),regard (V e i) (Demo.flat t)):=by
 have he {K}(r q:Tray I)(h:∀ i≠0,V K i=0): dubbed V K r=dubbed V K q:=by
    unfold dubbed;apply Finset.sum_congr rfl; intro i _;rcases i with _|i
    · rw [volume_s _ _ (r.base∪q.base) (Finset.subset_union_left),volume_s _ _ (r.base∪q.base) Finset.subset_union_right];simp [fret]
    simp [h _ (Nat.succ_ne_zero _),volume]
 unfold announced tap at hh; rw [PowerSeries.coeff_mk,PowerSeries.coeff_mk,Finset.sum_range_succ,Finset.sum_range_succ,show (∑ i∈range e,tap (e-i) (dubbed V i s)) = ∑ i∈range e,tap (e-i) (dubbed V i t) from Finset.sum_congr rfl fun i hi=>by rw [he s t (h i (mem_range.mp hi))]] at hh
 have ht:=add_left_cancel hh; rw [Nat.sub_self,dubbed,dubbed] at ht
 rw [map_sum,map_sum] at ht
 simpa only [← show ∀ x:Dig,tap 0 x=PowerSeries.coeff 0 x from fun _=>rfl,regard_at] using ht

private lemma read_powers (N:ℕ)(A:ℕ→ℝ)(h:∀ x:ℝ,(∑ i∈range N,x^i*A i)=0):∀ i<N,A i=0:=by
 let p:= ∑ i∈range N,Polynomial.X^i*Polynomial.C (A i)
 have hp:p=0:=Polynomial.funext (by intro x;simpa [p,Polynomial.eval_finsetSum,Polynomial.eval_mul,mul_comm (A _) _] using h x)
 intro i hi
 have he :p.coeff i=0:=by rw [hp];simp
 unfold p at he; rw [Polynomial.finsetSum_coeff] at he
 simpa [Polynomial.coeff_mul_C,eq_comm,hi] using he

/-- Extract each rank under a germ gauge law, allowing other curvature corrections at
higher or scalar orders. Apply also to scalar reading transformations, Signed, adjoint. -/
lemma sorting (V:Script I)(e:ℕ)(s t:Demo I)(h:∀ k<e,∀ i≠0,V k i=0)
    (he:∀ x:ℝ,∃ a b:Tray I,(Demo.flat a).play=x • s.play ∧ (Demo.flat b).play=x • t.play ∧ tap e (announced V a)=tap e (announced V b))(j:ℕ)(hj:j≤e+2):
    regard (V e j) s=regard (V e j) t:=by
  have hh(x:ℝ):(∑ i∈range (e+3),x^i*(regard (V e i) s-regard (V e i) t))=0:=by
    obtain ⟨a,b,ha,hb,hg⟩:=he x
    have H:=detour a b h hg;simp_rw [regard_slug _ ha,regard_slug _ hb] at H
    simp_rw [mul_sub,Finset.sum_sub_distrib,H,sub_self]
  exact sub_eq_zero.mp (read_powers (e+3) _ hh j (by omega))
end YM.RG08.Gallery
