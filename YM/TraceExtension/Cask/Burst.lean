import YM.TraceExtension.Cask.Pebble
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open scoped Classical
variable {V L W I:Type}[DecidableEq V][DecidableEq I][DecidableEq L][DecidableEq W]{n:Side}[Fintype V][Fintype I][Fintype L][Fintype W]{G:Gauge}{R:Rep G n}(C:TourC R V L W)
local notation "P"=> agency C
local notation "y!"=> R.p.threshold
local notation "N!"=>lance C
-- Actor hit compressor for disjoint actor lots.
lemma painter (e h:ℝ)(he:0 ≤ h)(f:W→ℝ)(hf:∀ i,0 ≤ f i)(hp:∀ i,∑ j∈univ.filter (fun j=>C.who j=i), f j*Real.exp (e*coverNumber R.p.B (C.size j)) ≤ h)(ht:∀ i j,C.who i≠C.who j→ Disjoint (C.size i) (C.size j)): Hit C.size R.p.B f e h:=by
    intro i; let v(j):=if i∈C.size j then f j*Real.exp (e*coverNumber R.p.B (C.size j)) else 0; have h₀(j):0 ≤ v j:=by unfold v; split; exact mul_nonneg (hf _) (Real.exp_pos _).le;exact le_rfl
    refine ⟨h₀,Summable.of_finite,?_⟩; rw [tsum_fintype]; by_cases hk:∃ j,i∈C.size j; swap; · rw [sum_eq_zero (fun j _=>if_neg fun he=> hk ⟨j,he⟩)]; exact he
    obtain ⟨j,hj⟩:=hk; let t:=univ.filter (fun p=> i∈ C.size p); rw [← Finset.sum_filter]; apply le_trans _ (hp (C.who j)); refine sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _=> mul_nonneg (hf _) (Real.exp_pos _).le); exact fun k he=> mem_filter.mpr ⟨mem_univ _,of_not_not fun hz=> disjoint_left.mp (ht k j hz) (mem_filter.mp he).2 hj⟩
lemma transK {S T:Type} [Fintype S][Fintype T](W V) (U:S→Support n)(T':T→Support n)(f:S→ℝ)(g:T→ℝ)(e z:ℝ)(H:Hit U W f V e)(h:Hit T' W g V z): Hit (Sum.elim U T') W (Sum.elim f g) V (e+z):=by
    intro i; refine ⟨?_, Summable.of_finite,?_ ⟩;swap;· rw [tsum_fintype,Fintype.sum_sum_type]; exact add_le_add (Extra.Multi.Budget.cap (H i) _) (Extra.Multi.Budget.cap (h i) _)
    rintro (i|i); exact (H _).1 i; exact (h _).1 i
lemma tollC (e m:ℝ)(S: Finset (LandC C))(H:Woven P S)(a b: LandC C→ℝ)(he:1 ≤ m)(hw:1 ≤ e)(hv:∀ i,0≤a i)(ht:∀ i, a i* (if (P|>.shop i) then e/m else m^((P|>.cast i).card)) ≤ b i):
    e^(crew P S).card * (∏ i∈S,a i) ≤ ∏ i∈S,b i:=by
    have hg:0 < m:=zero_lt_one.trans_le he; let Q:= fun i=> if (P|>.shop i) then e/m else m^((P|>.cast i).card); have hQ i:0≤Q i:=by unfold Q; split; exact div_nonneg (zero_le_one.trans hw) hg.le; positivity
    calc
       _ ≤ (∏ i∈S,a i)*(∏ i∈S,Q i):= ?_
       _ = ∏ i∈S,a i*Q i:= Finset.prod_mul_distrib.symm
       _ ≤ _:= prod_le_prod (fun i _=>mul_nonneg (hv _) (hQ _)) (fun i _=> ht i)
    rw [mul_comm]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun i _=>hv _)
    rw [prod_sum_eq_prod_toLeft_mul_prod_toRight (s:=S)]
    let v:= crew P S; have h₀ : v=S.toLeft.image C.who:=by
        ext p; constructor
        · intro h; obtain ⟨i,hi,_⟩:= H.actor p h; rcases i with i|i
          · exact mem_image.mpr ⟨i,mem_toLeft.mpr hi.1,(mem_singleton.mp hi.2.1).symm⟩
          have hx: false=true:= hi.2.2; contradiction
        intro h; obtain ⟨i,hi,rfl⟩:=mem_image.mp h; exact mem_biUnion.mpr ⟨_,mem_toLeft.mp hi,mem_singleton_self ..⟩
    have hp : ∏ x∈S.toLeft,Q (.inl x)=(e/m)^v.card:=by
        rw [prod_congr (f:=fun i=>Q (.inl i)) rfl (g:=fun _=>e/m) (fun i _=>if_pos rfl),prod_const,h₀,card_image_of_injOn]; intro i hi j hj hh
        have hk: C.who i∈v:= mem_biUnion.mpr ⟨_,mem_toLeft.mp hi,mem_singleton_self _⟩; exact Sum.inl.inj ((H.actor _ hk).unique (show _∧_ from ⟨mem_toLeft.mp hi,mem_singleton_self _,show (agency C).shop (.inl i) from rfl⟩) (show _∧_ from ⟨mem_toLeft.mp hj, hh.symm ▸ mem_singleton_self _,show (agency C).shop (.inl j) from rfl⟩))
    have hz : v.card ≤ ∑ t∈S.toRight, ((agency C).cast (.inr t)).card:= by
       refine le_trans (card_le_card (t:=joinP (agency C) S) ?_) (Finset.card_biUnion_le ..); intro p hp; obtain ⟨t,ht,hq,hv⟩:= H.host p hp; rcases t with t|t
       · exact False.elim (hv rfl)
       exact mem_biUnion.mpr ⟨_,mem_toRight.mpr ht,hq⟩
    rw [hp,prod_congr (f:=fun i=>Q (.inr i)) rfl (g:=fun x=> m^((agency C).cast (.inr x)).card) (fun i _=> if_neg (fun h=>by have he: false=true:=h; contradiction)),Finset.prod_pow_eq_pow_sum]
    apply le_trans ?_ (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ he hz) (pow_nonneg (div_nonneg (zero_le_one.trans hw) hg.le) _)); exact (by rw [div_pow,div_mul_cancel₀ _ (pow_pos hg _).ne'])
end YM.Trace.Cask
