import YM.WilsonBulk.Recast.Parity
import YM.WilsonBulk.Tuning.Voyage

/-!
# Scaling grades of links coherently. Step on any coupling-ratio words X:
  Ω contact code F(X,a)=Z(X*r, (1/r) • a).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Recall
open PowerSeries Filter Function Finset Matrix Sheet Equiv
open scoped Topology Classical BigOperators
variable {α β A B : Type} [CommRing A] [Algebra ℝ A] {n i j d : ℕ}

abbrev Word := PowerSeries ℝ
def color_clock (α : Type) : Word→ₐ[ℝ]Tape α := tuner ((post (Formula α)).comp (Algebra.ofId ℝ _)) (g:=X) constantCoeff_X
lemma tonic (g : Word) (x : β→Tape α) : submit x (color_clock β g)=color_clock α g := by
  apply DFunLike.congr_fun (f:=(submit x).comp (color_clock β)); apply bar_ext_aux
  · rw [AlgHom.comp_apply,color_clock,tuner_X,submit_X,constantCoeff_X]
  · rw [AlgHom.comp_apply,color_clock,tuner_X,submit_X,color_clock,tuner_X]
  intro a; exact Eq.trans (show ((submit x).comp (color_clock β)) _ =algebraMap ℝ _ a from ((submit x).comp (color_clock β)).commutes a) ((color_clock α).commutes a).symm -- algebraMap vs C
lemma tonic_X (α : Type) : color_clock α X=X := by rw [color_clock,tuner_X]
lemma tonic_C (x : ℝ) : color_clock α (C x)= algebraMap ℝ _ x := (color_clock α).commutes x
lemma tonic_coeff (p : Word) (i : ℕ) : coeff i (color_clock α p)=MvPolynomial.C (coeff i p) := by
  calc _ = coeff i (color_clock α (∑ j ∈ range (i+1), X^j*C (coeff j p))) := (Steps.push (color_clock α) (by rw [tonic_X, constantCoeff_X]) (before_end (i+1) p)) i (by omega)
       _ = _ := by
          simp only [map_sum,map_mul,map_pow,tonic_X,tonic_C, PowerSeries.algebraMap_apply]; simp [coeff_mul_C, coeff_X_pow]

def shade (g r : Word) := code (fun i:α=> color_clock α r*named i) (g:= X*color_clock α g) (by simp)
lemma shadeX (g r : Word) : shade g r (α:=α) X=X*color_clock α g := by rw [shade,code_X]
lemma shade_name (g r : Word) (i : α) : shade g r (named i)=color_clock α r*named i:= by rw [shade,code_named]

variable [Fintype α]
omit [Fintype α] in
lemma script_energy (v : Legs α n) (g r : Word) : shade g r (C (field v))=color_clock α r^n * C (field v) := by
  simp only [field,map_prod, show ∀ x:α,shade g r (C (MvPolynomial.X x))=_ from fun x=>shade_name g r x,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
omit [Fintype α] in
lemma shade_door (g r : Word) (v : ℝ) : shade g r (α:=α) (C (MvPolynomial.C v))= C (MvPolynomial.C v) := by
  rw [shade,code_C,MvPolynomial.aeval_C, PowerSeries.algebraMap_apply]; rfl
lemma script_shift (u : Page α n) (g r : Word) : shade g r (C (script u))=color_clock α r^n * C (script u) := by
  unfold script; simp only [map_sum,map_mul,script_energy,mul_sum,shade_door]; exact sum_congr rfl (fun i _=> by rw [mul_left_comm])

variable {g r : Word}
lemma shade_contact (h : g*r=1) (p : Page α (n+1)) : shade g r (X^n*C (script p))=color_clock α r*(X^n*C (script p)) := by
  rw [map_mul,map_pow,shadeX,script_shift,mul_pow,pow_succ]; suffices hx : color_clock α g^n*color_clock α r^n=1 by
    rw [show X^n*_*(_*_*C (script p))=color_clock α r*(X^n*((color_clock α g^n*color_clock α r^n)*C (script p))) by ring,hx,one_mul]
  rw [← mul_pow, ← map_mul,h,map_one,one_pow]
lemma exposes (hf : g*r=1) (u : Tabletop α→Tabletop β) (i : β) : shade g r (exposure u i)=color_clock α r*exposure u i := by
  let s:=fun v=> u v i; let p:=exposure u i
  ext1 m
  have ht : Steps (m+1) p (∑ k∈range (m+1),X^k*C (script (photo s (k+1)))) := by
    have hx k : coeff k p=script (photo s (k+1)):= by rw [show p=zoom (ink s) from rfl,zoom_power,ink_power]
    have he := before_end (m+1) p; simp_rw [hx] at he; exact he
  exact (Steps.push (shade g r) (by rw [shadeX];simp) ht m (by omega)).trans (Eq.trans (by simp only [map_sum,shade_contact hf,mul_sum]) (Steps.mul Steps.self ht m (by omega) |>.symm)) -- ambiguity

omit [Fintype α] in
lemma pollutions (t : α→Tape β) (h : ∀ i, shade g r (t i)=color_clock β r*t i) : (submit t).comp (shade g r)=(shade g r).comp (submit t) := by
  refine code_ext _ _ ?_ ?_ ?_
  · rw [AlgHom.comp_apply, shadeX,map_mul,submit_X,map_mul,constantCoeff_X,zero_mul]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, shadeX,map_mul,submit_X, tonic,shadeX]
  intro i; rw [AlgHom.comp_apply,AlgHom.comp_apply,shade_name,map_mul,submit_named, tonic, h i]
lemma around_bar (T : Tabletop α→Tabletop β) (p : Tape β) (hf : g*r=1) : submit (exposure T) (shade g r p)=shade g r (submit (exposure T) p) := DFunLike.congr_fun (pollutions (exposure T) (exposes hf T)) p
lemma authority {G : Gauge} (T : Lattice.Side) {V : Atelier.Logbook G T} (hf : g*r=1) (h : Parapet.Regime V) : Parapet.Regime (shade g r V) := by -- G implicit
  constructor
  · intro s b; rw [Atelier.Spins,around_bar _ V hf,h.spins s b]
  intro i; rw [Sheet.mountain,← upper_code, around_bar _ V hf, h.dance i,around_bar _ V hf,upper_code]; rfl
end YM.WilsonBulk.Recall
