import YM.RG08.Carrel.Aline

/-!
# Stencil weights of higher jets. fake period dimensions paid task-polynomial, not repeated
on every step. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Carrel
open Camera Cloud Room Glyph
open Lattice Laurent Forms Pert.Bulk Isles Packets Filter Finset Function RG
open Wilson Exterior Push.Uniform Precision Work.F03 Extra.Iteration
open scoped Topology BigOperators ContDiff Classical ENNReal
variable {G:Gauge}{n N:ℕ}

private lemma teens (r:ℕ)(i:Tape N (Bedge G (attic r))):shelf (reach ∘ i)≤ 8*r:=by
 rw [shelf_diam];apply Ground.radius_le _ _ (by positivity);intro a b
 have h : Laurent.size ((lift (i a).1)-(lift (i b).1))≤8*r:=by
    apply le_trans (b:= size (lift (i a).1)+size (-(lift (i b).1)))
    · exact size_add ..
    rw [size_neg];have h:=attic_left r (i a).1;have T:=attic_left r (i b).1;omega
 change ((size _:ℕ) : ℝ)≤_
 exact_mod_cast h
private lemma cardAttic (G:Gauge) (r N:ℕ):
 Fintype.card (Tape N (Bedge G (attic r)))≤((2^4*Fintype.card (Rayk G 1))^N)*(1+r)^(4*N):=by
 have he: Fintype.card (Tape N (Bedge G (attic r)))=(((2*r+1)^4)*(Fintype.card (Rayk G 1)))^N:=by
    have he:Fintype.card (Tape N (Bedge G (attic r)))=(Fintype.card (Site (attic r)×Rayk G 1))^N:=Fintype.card_pi_const _ _
    rw [he,Fintype.card_prod,site_card];rfl
 rw [he,pow_mul,←mul_pow]; apply Nat.pow_le_pow_left
 apply le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (show 2*r+1≤2*(1+r) by omega) 4))
 simp only [mul_pow]; exact le_of_eq (by ring)

open Planned.PrimaryIntegral295 in
lemma store_paid (G:Gauge){σ:ℝ}(h:0<σ)(n N:ℕ):∃ C:ℝ,0≤C∧∀ (a:Atom G n), Won (stored a N) (σ/32) (a.budget σ * C):=by
 -- useful spare: slide weight spend 8*σ/32, deck pays σ/4, fake period sum σ/4
 let η:=σ/4
 obtain ⟨K,hK,h⟩:=per_deck G n N (η:=η) (by unfold η; linarith)
 let Q:ℕ:=(2^4*Fintype.card (Rayk G 1))^N
 let D:ℝ:=Carrier.widthCost η (4*N)
 let C:ℝ:=(Q:ℝ)* D * K
 have hd:1≤D:=Carrier.widthCost_ge (by unfold η; positivity) (4*N)
 have Kpos:0<K:=by linarith
 have Dpos:0<D:=by linarith
 have hc:0≤C:=by unfold C; positivity
 refine ⟨C,hc,fun a=>⟨mul_nonneg (by unfold Atom.budget Atom.magnitude; positivity) hc,?_⟩⟩
 let I:=Tape N (Bedge G (attic a.length))
 let f(i:I):=Camera.deck N (showAtom a (0:Site (attic a.length))) i
 let B (i:I) (x:Slide (Rayk G 1) N):= if x=(reach ∘ i) then f i else (0:ℝ)
 let L:ℝ:=a.length
 calc
  Cost _ _ ≤∑' (x:Slide (Rayk G 1) N),∑ i:I,bill (B i x) (σ/32*shelf x):=ENNReal.tsum_le_tsum (fun x=>bill_sum _ _)
  _ =∑ i:I,bill (f i) (σ/32*shelf (reach ∘ i)):=?_
  _ ≤ ENNReal.ofReal (∑ i:I,(a.budget η*K)*Real.exp (η*L)):=by
        simp_rw [ENNReal.ofReal_sum_of_nonneg (f:=fun _:I=>a.budget η*K*Real.exp (η*L)) (by intros;unfold Atom.budget Atom.magnitude; positivity)];apply Finset.sum_le_sum;intro i _;unfold bill;apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul (h ..) _ (Real.exp_pos _).le (by unfold Atom.budget Atom.magnitude;positivity); exact Real.exp_le_exp.mpr (by have he:=teens a.length i; unfold η L; nlinarith)
  _ ≤ _:=by
        apply ENNReal.ofReal_le_ofReal;rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        have he : (↑(Fintype.card I):ℝ)≤(Q:ℝ)* (1+L)^(4*N):=by unfold Q I L;exact_mod_cast cardAttic G a.length N
        have hp : (1+L)^(4*N)≤D* Real.exp (η*L):=Carrier.widthBill η (by unfold η; positivity) _ _ (by unfold L; positivity)
        have hu:=a.magnitude; have hv:0≤a.magnitude:=by unfold Atom.magnitude; positivity
        unfold Atom.budget;change ↑(Fintype.card I)*(a.magnitude*Real.exp (η*L)*K*_)≤_
        calc
         _ ≤ ((Q:ℝ)*(D*Real.exp (η*L))) *(a.magnitude*Real.exp (η*L)*K*_) := mul_le_mul_of_nonneg_right (he.trans (mul_le_mul_of_nonneg_left hp (by positivity))) (by positivity)
         _ = a.magnitude*((Q:ℝ)*D*K)* Real.exp ((3*η)*L):=by rw [show 3*η*L=(η*L+η*L)+η*L by ring, Real.exp_add,Real.exp_add];ring
         _ ≤ _ :=by rw [mul_right_comm]; unfold C;apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (show 3*η≤σ by unfold η; linarith) (by unfold L; positivity))) hv) hc
  -- ennreal commute finitely
 have he (x:Slide (Rayk G 1) N): (∑ i:I,bill (B i x) (σ/32*shelf x))=∑' i:I,bill (B i x) (σ/32*shelf x):= (tsum_fintype _).symm
 simp_rw [he];rw [ENNReal.tsum_comm,tsum_fintype];apply Finset.sum_congr rfl;intro i _;unfold B;simp only [bill,apply_ite abs,abs_zero,ite_mul,zero_mul,apply_ite ENNReal.ofReal,ENNReal.ofReal_zero];rw [tsum_ite_eq]
end YM.RG08.Carrel
