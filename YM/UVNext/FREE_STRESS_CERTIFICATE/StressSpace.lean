import YM.UVNext.FREE_STRESS_CERTIFICATE.Parity
import YM.UVNext.FREE_STRESS_CERTIFICATE.Rest

/-! Signed-coordinate orbit computation on `KernelSpace`. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Climb Table Work.A01 Next.UVStress Function Set Submodule
variable {G : Gauge} (F : Frames G) (H : (freeTable F).RealSpin) (hG : G.Simple)
variable (J : KernelSpace H)

lemma perm_tensor (p : Wheels) (a b : Axis) : ride F H 4 p (J.val a b) = J.val (p a) (p b) := by
  unfold ride
  rw [tensor_column (sym_mem.mp (kernel_mem.mp J.property).1).2.2, eps_round,eps_round]; simp [round]

lemma color_tensor (i j : Axis) : swatch F H 4 (fun t => bit t i*bit t j) (J.val i j) := by
  intro t
  rw [tensor_column (sym_mem.mp (kernel_mem.mp J.property).1).2.2,eps_mirror_bit,eps_mirror_bit]; push_cast; rfl

include hG in
private lemma core_diag : J.val 0 0 ∈ span ℂ { (freeTable F).unit 4, near F 0, far F 0 } := by
  let U := span ℂ {(freeTable F).unit 4, near F 0, far F 0}
  have H1 : (freeTable F).unit 4 ∈ U := subset_span (by simp)
  have H2 : singles (fun i => flat F 0 i 0 i)∈U := near_zero F ▸ subset_span (by simp)
  have H3 : pairs (fun i j => flat F i j i j)∈U := far_zero F ▸ subset_span (by simp)
  have ht (p : Wheels) (_h : p 0=0) : ride F H 4 p (J.val 0 0)=J.val 0 0 := by rw [perm_tensor,_h]
  apply secure F H _ ht
  let χ (t : Axis) := bit t 0 * bit t 0
  apply align F H _ χ (binary_compose (binary_bit _) (binary_bit _)) (color_tensor F H J 0 0) _ _ (spanFour hG)
  rintro _ (rfl|⟨i,k,rfl⟩)
  · rw [pin_unit]; refine ⟨fun _ => 1,binary_unit,unit_color F H _,fun _ => ?_⟩
    change revolving F H 4 ((freeTable F).unit 4) ∈ U
    rw [revolve_value]; simp only [around,ride_unit]
    exact U.add_mem (U.add_mem (U.add_mem (U.add_mem (U.add_mem H1 H1) H1) H1) H1) H1
  refine ⟨fun t => zob i t*zob k t,binary_compose (binary_plane i) (binary_plane k),
    link_color F H _ _ _ _ le_rfl, fun he => ?_⟩
  obtain ⟨-,rfl⟩|⟨c,_,_,hx,_⟩ := even_format i k 0 fun t => congr_fun he.symm t
  · obtain ⟨⟨a,b⟩,hp⟩ := i
    change flat F a b a b∈U.comap (revolving F H 4)
    change a < b at hp
    have hb : b≠0 := (lt_of_le_of_lt (Fin.zero_le _) hp).ne'
    rcases eq_or_ne a 0 with rfl|ha
    · exact harvest_single F H (fun b => flat F 0 b 0 b) b hb (fun p hw => by simp only [flat,ride_link,hw]) U H2
    exact harvest_pair F H (fun a b => flat F a b a b) a b ha hb hp.ne (fun p _ => by simp only [flat,ride_link]) U H3
  exact (hx rfl).elim

include hG in
lemma diag_full : ∃ a b : ℝ, J.val 0 0 = a • near F 0 + b • far F 0 := by
  have h : J.val 0 0 ∈ span ℝ {(freeTable F).unit 4, near F 0, far F 0} := by
    apply to_real F H _ _ _ _ (core_diag F H hG J)
    · intro i hi; simp only [mem_insert_iff,mem_singleton_iff] at hi
      rcases hi with rfl|rfl|rfl
      exacts [(freeTable F).conj_unit H _,panel_star F H _ _, far_star F H _]
    exact (sym_mem.mp (kernel_mem.mp J.property).1).2.1 ..
  rw [Set.insert_eq,span_union,mem_sup] at h
  obtain ⟨y,hy,z,hz,h⟩ := h
  obtain ⟨c,rfl⟩ := mem_span_singleton.mp hy
  obtain ⟨a,b,rfl⟩ := mem_span_pair.mp hz
  have he := congr_arg (fun v => expectation (freeTable F) 4 v) h
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_add,map_smul,mean_unit (table_regular F),
    near,panel_mean,far_mean, (kernel_mem.mp J.property).2, mul_zero,add_zero,smul_eq_mul,mul_one] at he
  have he : c=0 := Complex.ofReal_eq_zero.mp he
  subst c; exact ⟨a,b,by simpa using h.symm⟩

include hG in
private theorem core_off : J.val 0 1 ∈ span ℂ {panel F 0 1} := by
  let U := span ℂ {panel F 0 1}
  let V := U.comap (lastPair F H 4)
  let χ t := bit t 0*bit t 1
  apply securing F H _ (by rw [perm_tensor]; simp [l23,Equiv.swap_apply_def])
  apply align F H _ χ (binary_compose (binary_bit _) (binary_bit _)) (color_tensor F H J 0 1) V _ (spanFour hG)
  rintro _ (rfl|⟨i,k,rfl⟩)
  · rw [pin_unit]; refine ⟨fun _ => 1,binary_unit,unit_color F H _,fun h => ?_⟩
    have hh := congr_fun h (0:Axis); norm_num [χ,bit] at hh
  refine ⟨fun t => zob i t*zob k t,binary_compose (binary_plane i) (binary_plane k),link_color F H _ _ _ _ le_rfl, fun h => ?_⟩
  have he (a : Axis) (ha : a ≠ 0) (ht : a ≠ 1) : flat F 0 a 1 a∈V := by
    change flat F _ a _ a + ride F H _ l23 _ ∈ U
    dsimp only [flat]; rw [ride_link,show l23 0=0 by decide,show l23 1=1 by decide]
    let f := fun i => flat F 0 i 1 i
    change f a + f (l23 a) ∈ U
    rw [two_one f a ha ht, ← panel_one]; exact subset_span (mem_singleton _)
  rcases even_format i k 1 (fun t => congr_fun h.symm t) with ⟨hf,-⟩|⟨a,h1,h2,h3,⟨h4,h5⟩|⟨h4,h5⟩⟩
  · exact ((by decide : (1:Axis) ≠ 0) hf).elim
  · exact click_link F i k 0 a 1 a h4 h5 le_rfl V (he a h1 h2)
  rw [two_flip _ i k]
  exact click_link F k i 0 a 1 a h4 h5 le_rfl V (he a h1 h2)

lemma off_full (hG : G.Simple) : ∃ c : ℝ, J.val 0 1 = c • panel F 0 1 := by
  have h := core_off F H hG J
  obtain ⟨c,hc⟩ := mem_span_singleton.mp (to_real F H _ (by
    rintro b hb; rw [mem_singleton_iff] at hb; subst b; exact panel_star F H ..) _
    ((sym_mem.mp (kernel_mem.mp J.property).1).2.1 ..) h)
  exact ⟨c,hc.symm⟩

lemma determined (Q : KernelSpace H) (h : J.val 0 0=Q.val 0 0) (k : J.val 0 1 = Q.val 0 1) : J=Q := by
  apply Subtype.ext; funext a b
  let f : Wheels := Equiv.swap 0 a
  have hf : f 0=a := by simp [f]
  rcases eq_or_ne b a with rfl|he
  · exact (show J.val b b = Q.val b b from by
      have h' := congr_arg (ride F H 4 f) h; simpa only [perm_tensor,show f 0=b from hf] using h')
  let p := Equiv.swap (f 1) b * f
  have he' : f 0 ≠ f 1 := f.injective.ne (by decide)
  have hp : p 0=a := by simp [p,Equiv.swap_apply_def,hf,he.symm,show a≠f 1 from hf ▸ he']
  have ht : p 1=b := by simp [p]
  have h := congr_arg (ride F H 4 p) k
  simpa only [perm_tensor,hp,ht] using h

def paintStress (a b c : ℝ) := a • east F + b • west F + c • across F

theorem fits (a b c : ℝ) : paintStress F a b c ∈ KernelSpace H :=
  (KernelSpace H).add_mem ((KernelSpace H).add_mem ((KernelSpace H).smul_mem _ (east_on F H))
    ((KernelSpace H).smul_mem _ (west_on F H))) ((KernelSpace H).smul_mem _ (across_on F H))

include hG in
theorem exhaust : ∃ a b c : ℝ, J.val = paintStress F a b c := by
  obtain ⟨a,b,h⟩ := diag_full F H hG J
  obtain ⟨c,hc⟩ := off_full F H J hG
  let U : KernelSpace H := ⟨_,fits F H a b c⟩
  have he : J=U := determined F H J U (by simpa [U,paintStress,east,west,splitDiag,across] using h)
    (by simpa [U,paintStress,east,west,splitDiag,across] using hc)
  exact ⟨a,b,c,congr_arg Subtype.val he⟩

end YM.UVNext.FreeStress
