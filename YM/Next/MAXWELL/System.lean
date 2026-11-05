import YM.Next.MAXWELL.Caps
import YM.Next.MAXWELL.Mark
import YM.Next.MAXWELL.Stress
import YM.Work.B08
import YM.Work.B10
import YM.Work.D06





/-!
# RPort0: hierarchy, ranks and derivatives

On an arbitrary frame register; no film inputs from the Wilson (nonabelian)
problem. Faithful on the specific continuum free Comparator. Also build
the eventual *same* Rotation and normalized J labels now (normalizing
parameter τ will include both signs).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Wick
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder
variable {G : Gauge} (F : Labels.Frames G) {d n : ℕ}

abbrev Model := freeTable F

lemma target_labels (d : ℕ) : (Model F).null d=LinearMap.ker (snap F d) := by
  ext q
  rw [← projectionExact F,no_residual, Submodule.mem_bot]; rfl

def fields (d : ℕ) : (Model F).Field d ≃ₗ[ℂ] ↥(shellSector G d) :=
  (Submodule.quotEquivOfEq _ _ (target_labels F d)).trans <|
    (snap F d).quotKerEquivOfSurjective (full F d)

lemma fields_eval (v : (standard F).Ref d) : fields F d ((Model F).project d v) = snap F d v := rfl

def address (d : ℕ) := (shellSector G d).subtype.comp (fields F d).toLinearMap

lemma address_eval (d) (v : (Model F).Field d) : address F d v = (fields F d v).val := rfl
lemma address_in (d) (v : (Model F).Field d) : address F d v ∈ shellSector G d := (fields F d v).property

lemma address_inj (d) : Injective (address F d) := Subtype.val_injective.comp (fields F d).injective

def supply (x : (Model F).Tag) := address F x.1 x.2

lemma display (p : Fin n → (Model F).Tag) {x : Points n} : (Model F).useAt (Model F) x p = moment G x (supply F ∘ p) := by
  change moment G x _ = _; congr 1; ext1 i
  change (snap F _ ((Model F).representative _ ((p i).2))).val = (fields F (p i).1 (p i).2).val
  rw [← fields_eval, Table.rep]

lemma address_star {H : (Model F).RealSpin} {d : ℕ} (p : (Model F).Field d) :
    address F d ((Model F).conj H d p) = realForm (address F d p) := by
  obtain ⟨v,rfl⟩ := (Model F).onto d p
  rw [Table.conj_project, address_eval,address_eval,fields_eval,fields_eval]
  exact ready_bar F (⟨d,v⟩ : (standard F).Token)

lemma address_motion {H : (Model F).RealSpin} (s : Signed) {d : ℕ} (p : (Model F).Field d) :
    address F d ((Model F).mirror H d s p) = reflectPol s.ortho (address F d p) := by
  obtain ⟨v,rfl⟩ := (Model F).onto d p
  rw [Table.mirror_project, address_eval,address_eval,fields_eval,fields_eval]
  exact ready_signed F s (⟨d,v⟩ : (standard F).Token)

lemma unit_address (d : ℕ) : address F d ((Model F).unit d)=1 := by
  rw [Table.unit,address_eval,fields_eval]
  change observable G d ((F.level _).coords.symm ((standard F).scalar _)) = _
  rw [show (standard F).scalar d = (F.level d).coords (Labels.unit G d) by
    simp [standard, Register.scalar, Register.coord]; exact one_smul _ _,
    (F.level d).coords.symm_apply_apply]; exact map_one reduceEq

def slide {d l : ℕ} (D : Engine G l) (h : ∀ p ∈ shellSector G d, rewired D p ∈ shellSector G (d+l)) :
    (Model F).Field d →ₗ[ℂ] (Model F).Field (d+l) := (fields F _).symm.toLinearMap.comp <|
  (((rewired D).toLinearMap.comp (address F d)).codRestrict _ fun p => h _ (address_in F d p))

lemma moving {d l} (D : Engine G l) (h) (x : (Model F).Field d) : address F _ (slide F D h x) = rewired D (address F d x) := by
  rw [address_eval]
  unfold slide; simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]; rfl

def scheme : DiffPlan (Model F) where
  rise {d e} h := (fields F e).symm.toLinearMap.comp
    ((Submodule.inclusion (chain h)).comp (fields F d).toLinearMap)
  deriv _ a := slide F (glide G (basis a)) fun _ h => glide_holds _ h

lemma address_rise (e) (h : d≤e) (p : (Model F).Field d) :
    address F _ ((scheme F).rise h p)=address F _ p := by
  unfold scheme; rw [address_eval]; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]; rfl
lemma address_derive (d) (a : Axis) (p : (Model F).Field d) :
    address F _ ((scheme F).deriv d a p) = rewired (glide G (basis a)) (address F d p) := moving F _ (fun _ h => glide_holds _ h) _

lemma scheme_filters : (scheme F).Inclusions (Model F) where
  kernels {d e} h p {n x} hx w := by
    rw [display,display]; congr 1; ext1 i
    exact Fin.cases (address_rise F _ h p) (fun _ => rfl) i

lemma scheme_derives : (scheme F).Derivatives (Model F) where
  kernels d a p {n x} hx w := by
    simp_rw [display F]; rw [positionD _ hx 0 a]
    congr 1; ext1 i; refine Fin.cases ?_ (fun j => ?_) i
    · rw [update_self]; exact address_derive F d a p
    rw [update_of_ne (Fin.succ_ne_zero _)]; rfl

lemma phase_orientation : (scheme F).Orientation (spin_free F) :=
  Work.D06.compat (table_smooth F) (table_sym F) (spin_free F) _ (scheme_derives F) (scheme_filters F)

theorem hierarchy : (Model F).Hierarchy where
  laws := table_regular _
  spin := spin_free F
  translations _ x _ s _ := moment_across x _ s
  positive := positive_table F
  smooth := table_smooth F
  onTests := Work.B08.smear (table_regular F) (spin_free F) (table_smooth F) (positive_table F)
  order := Work.B10.answer (Model F) (Model F) (scheme F) (fun _ => le_rfl) (table_smooth F) (table_regular F)
    (scheme_filters F) (scheme_derives F) (fun _ d v => cap_moment (fun i => ready F (⟨d i,v i⟩ : (standard F).Token)))

def scopeRise (d : ℕ) (s : Ortho.Skew) : Module.End ℂ ((Model F).Field d) :=
  slide F (l:=0) (wheel G s) fun _ hp => wheel_holds _ hp



def tensorT (d : ℕ) (s : Ortho) : Module.End ℂ ((Model F).Field d) := (fields F d).symm.toLinearMap.comp
  (((reflectPol s).toLinearMap.comp (address F d)).codRestrict (shellSector G d) (by
    intro p
    change reflectPol s (address F d p)∈shellSector G d
    obtain ⟨q,hq⟩ := address_in F d p; exact ⟨Labels.tensor s q,(pulls_label ..).trans (by rw [hq])⟩))

lemma address_rot (d) (s : Ortho) (p : (Model F).Field d) : address F d (tensorT F d s p)=reflectPol s (address F d p) := by
  simp only [tensorT,address_eval,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]; rfl

lemma wheels_linear (s t : Ortho.Skew) (p : WickPol G) :
    rewired (wheel G (s+t)) p=rewired (wheel G s) p+rewired (wheel G t) p := by
  suffices H : rewired (wheel G (s+t))=rewired (wheel G s)+rewired (wheel G t) from DFunLike.congr_fun H p
  apply MvPolynomial.derivation_ext; intro i
  simp_rw [← symbol_coordinate i];
  simp only [Derivation.add_apply,rewired_symbol,wheel,map_add,LinearMap.add_apply]
  obtain ⟨L,hL⟩ := symbol_linear (G:=G) (i.1+0)
  exact (by simp_rw [← hL]; exact map_add L _ _)

lemma wheels_scalar (s : Ortho.Skew) (c : ℝ) (p : WickPol G) :
    rewired (wheel G (c • s)) p=(c:ℂ) • rewired (wheel G s) p := by
  suffices H : rewired (wheel G (c • s))=(c:ℂ) • rewired (wheel G s) from DFunLike.congr_fun H p
  apply MvPolynomial.derivation_ext; intro i
  rw [← symbol_coordinate i,Derivation.smul_apply]
  simp only [rewired_symbol,wheel,map_smul,LinearMap.smul_apply]
  obtain ⟨L,hL⟩ := symbol_linear (G:=G) (i.1+0)
  simp_rw [← hL]; rw [map_smul]
  exact RCLike.real_smul_eq_coe_smul (K:=ℂ) c _

lemma scopeRewrite (d) (s : Ortho.Skew) (x : (Model F).Field d) :
    address F d (scopeRise F d s x)=rewired (wheel G s) (address F d x) :=
  moving F (wheel G s) (fun _ hp => wheel_holds _ hp) x

def gear : Table.Rotation (Model F) where
  act d s := LinearEquiv.ofLinear (tensorT F d s) (tensorT F d s⁻¹)
    (by
      apply LinearMap.ext; intro v; apply address_inj F d
      simp only [LinearMap.comp_apply,address_rot]; rw [← pol_mul,mul_inv_cancel,pol_one]; rfl)
    (by apply LinearMap.ext; intro v; apply address_inj F d
        simp only [LinearMap.comp_apply,address_rot]; rw [← pol_mul,inv_mul_cancel,pol_one]; rfl)
  lie d :=
    { toFun s := scopeRise F d s
      map_add' s t := by
        apply LinearMap.ext; intro v; apply address_inj F d
        simp only [LinearMap.add_apply,map_add,scopeRewrite,wheels_linear]
      map_smul' z s := by
        apply LinearMap.ext; intro v; apply address_inj F d
        change address F d (scopeRise F d (z • s) v)= address F d (z • (scopeRise F d s v))
        rw [show address F d (z • scopeRise F d s v) = (z:ℂ) • address F d (scopeRise F d s v) by
          rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) z (scopeRise F d s v),map_smul]; rfl]
        rw [scopeRewrite, scopeRewrite,wheels_scalar] }

def original (a b : Axis) := (fields F 4).symm ⟨polStress G a b,stress_label G a b⟩

lemma inertia (a b : Axis) : address F 4 (original F a b)=polStress G a b := by simp [original,address_eval]

lemma realStress : Table.Conserved (scheme F) (spin_free F) (original F) where
  symmetric a b := address_inj F _ (by simp only [inertia,stress_sym a b])
  real a b := address_inj F _ (by rw [address_star,inertia,pol_real])
  divergence b := address_inj F _ (by simp_rw [map_sum,address_derive,inertia]; rw [pol_conservation,map_zero])


end YM.Maxwell.Free
