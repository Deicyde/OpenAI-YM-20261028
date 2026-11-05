import YM.RG08.Cairn.Shoot
/-!
# Finite aperture commuting
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Cairn
open Lattice Laurent Forms Pert.Bulk Isles Camera Carrel Glyph Room Exterior Function Stationary Bloch RG Finset MvPolynomial
open scoped BigOperators Classical ContDiff Topology ENNReal
variable {I J:Type}{n:ℕ}{P:Side}{σ τ c p:ℝ}

def city (e:I↪J):Cove P I↪ Cove P J :=⟨fun x=>(x.1,e x.2),fun i j h=>Prod.ext (show i.1=j.1 from congrArg (fun z:Cove P J=>z.1) h) (e.injective (congrArg Prod.snd h))⟩
lemma commuting (e:I↪J)(x:Tape n (Market I)): (port (I:=J) P ∘ (many (hide e) n x))=many (city e) n (port P ∘ x):=rfl
lemma install_view (e:I↪J)(i:Fin n)(F:Flake n (Market I)):
 pour (P:=P) (install e F) i=Function.extend (many (city e) n) (pour F i) 0:=by
 ext a :1;rw [pour,← (many (hide e) n).injective.tsum_eq (f:=_) ?hS]
 case hS =>
   rintro b hb;change _ ≠ 0 at hb; unfold Set.indicator at hb;by_contra! he; split at hb
   · exact hb (install_out _ _ he)
   exact hb rfl
 simp_rw [Set.indicator_apply,install_in]
 by_cases he:a∈Set.range (many (city e) n)
 · obtain ⟨d,rfl⟩:=he;rw [(many _ _).injective.extend_apply]
   unfold pour; apply tsum_congr; intro j; rw [Set.indicator_apply]; congr 1
   apply propext; unfold lantern; simp only [Set.mem_setOf,commuting,(many _ _).injective.eq_iff]
   change (hide e (j i)=hide e (reach (d i)) ∧ _)↔ _;rw [(hide e).injective.eq_iff]
 rw [Function.extend_apply' _ _ _ he]; have ht(b:Tape n (Market I)): many (hide e) n b∉lantern i a := fun hb=>he ⟨port P ∘ b,by rw [← commuting];exact hb.2⟩
 simp [ht]

variable [Fintype I][Fintype J]
lemma reindex (e:I↪J)(f:Flake n I):parley (Function.extend (many e n) f (0 : Flake n J))=rename e (parley f):=by
 unfold parley;rw [← Finset.sum_subset (s₁:=univ.image (many e n)) (subset_univ _) ?hz]
 case hz=> intro i hi he;rw [Function.extend_apply',Pi.zero_apply, zero_smul];rintro ⟨y,rfl⟩;exact he (mem_image_of_mem _ (mem_univ _))
 rw [Finset.sum_image (fun _ _ _ _ h=> (many e n).injective h),_root_.map_sum];apply Finset.sum_congr rfl;intro i _
 rw [(many e n).injective.extend_apply,_root_.map_smul,word,word,map_prod];simp only [rename_X];rfl

lemma install_poly (e:I↪J)(i:Fin n)(F:Flake n (Market I)):parley (pour (P:=P) (install e F) i)=MvPolynomial.rename (city e) (parley (pour F i)):=by rw [install_view,reindex]

-- subtraction/zero literal, for LP difference bills
omit [Fintype I] [Fintype J] in
lemma install_sub (u:I↪J)(F T:Flake n (Market I)): install u (F-T)=install u F-install u T:=by
 ext x :1;by_cases he:x∈Set.range (many (hide u) n)
 · obtain ⟨b,rfl⟩:=he;rw [Pi.sub_apply,install_in,install_in,install_in];rfl
 rw [Pi.sub_apply,install_out _ _ he,install_out _ _ he,install_out _ _ he,sub_self]
end YM.RG08.Cairn
