import YM.TraceExtension.Pi.Flux
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Kits
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det Loft MeasureTheory Source Source.Drops Work Planned.PrimaryIntegral295 Place Parts Next.Foundations WardBin StressFlux Labels
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge}{s:Side}{P:Support s}{F:Peat G s}{H:Hol G}(t:Fin 3→ℝ)
-- polar reading extracts divergence using tensor geometry
def prink (J:Jet G):Label G 4→ₗ[ℝ] ℂ:= ((Labels.read J).toLinearMap ∘ₗ (localFields G 4).subtype).restrictScalars ℝ
def prong (X Y:Taylor G 0) : Label G 4→ₗ[ℝ] ℂ:=
    prink (Pi.single 0 (X+Y))-prink (Pi.single 0 X)-prink (Pi.single 0 Y)+prink (0:Jet G)
lemma ivy_zero : ivy (G:=G) (0:Site s) (0:Taylor G 0)=0:=by
    have hp (i:Fin (2-1)) : variation (0:Taylor G i.val)=0:=by rw [← sampled_slot (d:=2) i (0:Taylor G i.val),Pi.single_zero,sampled_zero]
    have hx: variation (0:Taylor G 0)=0:=hp 0; unfold ivy; rw [hx]; exact map_zero edgeColor.symm
lemma ivy_plus (X Y:Taylor G 0):ivy (0:Site s) (X+Y)=ivy 0 X+ivy 0 Y:=by
    have hx (i:Fin (2-1))(X Y:Taylor G i.val) : variation (X+Y)=variation X+ variation Y:=by rw [← sampled_slot (d:=2) i X,← sampled_slot (d:=2) i Y,← sampled_add, ← Pi.single_add,sampled_slot]
    unfold ivy; rw [show variation (X+Y)=variation X+variation Y from hx 0 X Y,sC_add]
lemma sprig5 (X Y:Taylor G 0)(T:loom G s){w:Label G 4}(ht:JetTest H 0 w (Complex.ofRealCLM ∘ T.val))(h:G.Simple): prong X Y w= (↑(sheen (T.val) (ivy 0 X) (ivy 0 Y)):ℂ):=by
   have hp(J:Jet G): prink J w=(↑((1/2:ℝ)*sheen (T.val) (ivy 0 (J 0)) (ivy 0 (J 0))):ℂ):=by change Labels.read J w.val=_; rw[vista4 (T.property.1) h ht J,loom0,zero_add]
   rw[prong]; simp only [LinearMap.sub_apply,LinearMap.add_apply]; rw[hp,hp,hp,hp];simp only [Pi.single_eq_same]; rw[show ivy (0:Site s) ((0:Jet G) 0)=0 from ivy_zero, ivy_plus]
   have hh:sheen T.val 0 0=0:=by simp[sheen,iteratedFDeriv_two_apply]
   rw[hh,mul_zero, Complex.ofReal_zero,add_zero]; rw[sheen_add_r, sheen_symm (T.val) T.property.1 _ (ivy 0 X),sheen_symm T.val T.property.1 _ (ivy 0 Y), sheen_add_r,sheen_add_r, sheen_symm (T.val) T.property.1 (ivy 0 Y) (ivy 0 X)]; push_cast;ring
lemma prow (J:Jet G)(a r i s j:Axis): prong (J 0) (bentV (J 1) a) (pair G r i s j)= Labels.read J (pairDeriv G r i a s j+pairDeriv G s j a r i).val:=by
   have hp(x y:Taylor G 0): prong x y (pair G r i s j)=(↑(inner ℝ (curl0 r i x) (curl0 s j y)+inner ℝ (curl0 s j x) (curl0 r i y)):ℂ):=by
       unfold prong prink; simp only[LinearMap.add_apply,LinearMap.sub_apply,LinearMap.restrictScalars_apply,LinearMap.comp_apply,Submodule.subtype_apply]; change Labels.read _ _-Labels.read _ _-Labels.read _ _+ Labels.read _ _=_; simp_rw[pair_value]; simp only [Pi.single_eq_same,map_add, Pi.zero_apply, map_zero, inner_add_left,inner_add_right,inner_zero_left]; rw [real_inner_comm (curl0 r i y) (curl0 s j x)]; push_cast;ring
   rw[hp]; rw [Submodule.coe_add,map_add,pairDeriv_value,pairDeriv_value, bendV,bendV, Complex.ofReal_add]
def prance (J:Jet G)(t:Fin 3→ℝ)(b i:Axis):ℂ:= prong (J 0) (bentV (J 1) i) (stress G (Fin.cons 0 t) i b)
def princ (J:Jet G):Label G 5→ₗ[ℝ] ℂ:= ((Labels.read J).toLinearMap ∘ₗ (localFields G 5).subtype).restrictScalars ℝ
lemma pranced (J:Jet G)(b:Axis): (∑ i:Axis, prance J t b i)=princ J ((bareVector t).val b):=by
    let U:=prong (J 0) (bentV (J 1) b); let L:=princ J; let f:= prance J t b
    rw [← Finset.add_sum_erase _ f (mem_univ b),euler]
    rw [map_add (princ J)]; apply congr_arg₂
    · unfold f prance; rw[map_add (princ J),stress_of, if_pos rfl]; change U ((0:ℝ) • _+ t 0 • _+ t 1 • _)=_
      rw [zero_smul,zero_add,map_add]; apply congr_arg₂
      · rw [map_smul,map_smul,map_sum,map_sum]; apply congr_arg; exact sum_congr rfl fun j _=>prow J b b j b j
      rw [map_smul,map_smul]; apply congr_arg; rw [map_sum,map_sum]; apply sum_congr rfl; intro a _ ; rw [map_sum,map_sum]; exact sum_congr rfl fun j _=> prow J b a j a j
    rw [map_smul,map_sum, Finset.smul_sum]; apply sum_congr rfl; intro a ha; unfold f prance; rw [stress_of,if_neg (ne_of_mem_erase ha)]; change prong (J 0) (bentV (J 1) a) (t 2 • ∑ i:Axis,pair G a i b i)=t 2 • _; rw[map_smul,map_sum,map_sum]; apply congr_arg; refine sum_congr rfl fun j _=> ?_ ; rw [prow,add_comm (pairDeriv _ _ _ _ _ _)];rfl
set_option maxHeartbeats 200000 in
lemma prayer5 (b:Axis)(T:Axis→loom G s)(hl:∀ a, LocalOn P (T a).val)(hP:Nonwrapping P 0)(hs:40 ≤ s.val)(h:G.Simple){Z:Label G 5}
   (hV:∀ a,JetTest H 0 (stress G (Fin.cons 0 t) a b) (Complex.ofRealCLM ∘ (T a).val))(hz:JetTest H 0 Z (Complex.ofRealCLM ∘ airT (fun a=> (T a).val))): Z=(bareVector t).val b:=by
    refine label_ext (fun J=>?_) ; rw [readable T hl hP hs h hz, Complex.ofReal_sum]

    refine (sum_congr (g:=prance J t b) rfl (fun i _=> Eq.symm (show prance J t b i=_ from sprig5 (X:=J 0) (Y:=bentV (J 1) i) (T i) (hV i) h))).trans (show _=(Labels.read J) _ from pranced t J b)
end YM.Trace.Kits
