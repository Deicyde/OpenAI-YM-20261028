import YM.TraceExtension.Margin.Card
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Wicket Perfect Turret Weir Extra.Histories Next.Foundations Planned.PrimaryIntegral295 Place
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s:Side}{Φ:Peat G s}{H:Hol G}
variable (F:Frame G 4)(Z:Labels.Frame G 5) {R: Rep G s} {t:ℝ}
-- warp respects formal divergence even before PI equation projection.
def Ask(J:Jet G): F.Coeff→ₗ[ℝ] ℂ:= (prink J).comp (F.coords.symm.toLinearMap.restrictScalars ℝ)
def Sock(J:Jet G): Z.Coeff→ₗ[ℝ] ℂ:= (princ J).comp (Z.coords.symm.toLinearMap.restrictScalars ℝ)
def SighA (J:Jet G)(i:Axis):F.Coeff→ₗ[ℝ] ℂ:= (accord J i).comp (F.coords.symm.toLinearMap.restrictScalars ℝ)
abbrev pic(V: Axis→Axis→ F.Coeff)(b:Axis)(J:Jet G):= ∑ i, SighA F J i (V i b)
section herm
variable {h:G.Simple}{V:Axis→Axis→ F.Coeff}{Y:Axis→Z.Coeff}
set_option maxRecDepth 2048 in
lemma rot_v (A:Axis→Axis→ loom G s) (hA:∀ i j,JetTest H 0 (F.coords.symm (V i j)) (Complex.ofRealCLM∘(A i j).val)) (hp:∀ i,realBar (Z.coords.symm (Y i))=Z.coords.symm (Y i))(hq:∀ i j,realBar (F.coords.symm (V i j))=F.coords.symm (V i j))(h:G.Simple)(he:∀ k J,Sock Z J (Y k)=pic F V k J)(J:Jet G)(b:Axis): Sock Z J (Reed (Prism Z) Y b)=pic F (Plot (Prism F) V) b J:=by
    let U a m:=(rent*hued m a*hued m b) • Prism F m (V (prev m a) (prev m b))
    have hu : pic F (Plot (Prism F) V) b J=∑ i,∑ m:Motion, SighA F J i (U i m):= by unfold pic; refine Finset.sum_congr rfl fun a _=>?_; rw [plotEq]; exact map_sum (SighA F J a) (U a) univ
    rw[hu,reedEq,map_sum]; rw [sum_comm (s:=univ (α:=Axis))]; apply sum_congr rfl; intro i _; rw [map_smul]
    unfold U; obtain ⟨x,hx⟩:= i.1.perm.surjective b; rw [← hx]; let H':= i.1; have hX(c:Axis):prev i (i.1.perm c)=c:=i.1.perm.symm_apply_apply _
    have hu(c:Axis): hued i (i.1.perm c)=sign H' c:=by unfold hued; rw[hX]
    have hs : Sock Z J (Prism Z i (Y x))=Sock Z (shifted i.1 J) (Y x):=by unfold Sock; change Labels.read J (Z.coords.symm (Prism Z i (Y x))).val=Labels.read (StressFlux.shifted i.1 J) (Z.coords.symm (Y x)).val;rw[cloakR _ _ _ (hp x)]; exact eval_changed ..
    simp_rw [hX]; rw[hu,hs,he]; unfold pic; conv_rhs=> rw [← Equiv.sum_comp H'.perm];
    -- move rhs only
    rw [Finset.smul_sum]; apply sum_congr rfl; intro p _; rw [map_smul]; unfold H'; rw [hX,hu,patch_true F _ _ (hq p x),show SighA F J (i.1.perm p) (F.act i.1.ortho (V p x))=sign i.1 p • SighA F (StressFlux.shifted i.1 J) p (V p x) from psyche p i.1 (V p x) (A p x) (hA p x) h J]
    rw[smul_smul,show _*sign i.1 p= rent*sign i.1 x from ?_];
    dsimp only [H']; linear_combination (norm:=ring) (rent*sign i.1 x)*sign_sq i.1 p
end herm
-- cone quake
lemma prolA (x:Cone F): (fun i j=> F.coords.symm (x.val i j))∈ RawTwo G:=by
    let L: Module.End ℝ (Label G 4):=conjR
    exact (tensorMap (F.coords.symm.toLinearMap.restrictScalars ℝ) (K:=reflA F) (D:=spinR) (R:=reflB F) (T:=L)
            (fun s x=> F.coords.symm_apply_apply _) (fun v=> (show F.coords.symm (star v)=realBar (F.coords.symm v) from F.coords.injective (by ext i; rw[F.conj_basis,LinearEquiv.apply_symm_apply]; rfl))) x).property
lemma queenG(w:Fin 4→ℝ)(i:Axis) : Labels.read (0:Jet G) (stress G w i i).val=(w 0:ℂ):=by rw[stress_of, if_pos rfl]; simp[←Nat.cast_smul_eq_nsmul ℝ,Labels.unit,StressFlux.read_smul,pair_value,Complex.real_smul]
lemma armsQ (u:Motion)(v:F.Coeff)(hv:v 0=0): Ask F (0:Jet G) (Prism F u v)=0:=by
    change Labels.read _ (F.coords.symm (Prism F u v)).val=_; rw[vacancy]; change Motion.patch F u v 0=0; unfold Motion.patch; split; · change star (_:ℂ)=_; rw [Push.Local.act_at_zero,hv,star_zero]
    rw [Push.Local.act_at_zero,hv]
lemma wings (V: Axis→Axis→ F.Coeff)(he:∀ i j,V i j=V j i) (hv:∀ i j,V i j 0=0)(h:G.Simple) : ∃ w: Fin 3→ℝ, ∀ i j, F.coords (stress G (Fin.cons 0 w) i j)= Plot (Prism F) V i j:=by
   let W:= Plot (Prism F) V; obtain ⟨w,hw⟩:= labelStress_onto h ⟨fun i j=> F.coords.symm (W i j), prolA F ⟨W,shard F V he⟩⟩
   have he(i j:Axis) : stress G w i j=F.coords.symm (W i j):= congr_fun (congr_fun (congr_arg Subtype.val hw) i) j
   have hc:w 0=0:=by
        apply Complex.ofReal_eq_zero.mp; rw[←queenG w 0,he]; change Ask F 0 (W 0 0)=0;unfold W; rw[plotEq,map_sum]; apply Finset.sum_eq_zero; intro i _; rw [map_smul, armsQ F i _ (hv ..),smul_zero]
   exact ⟨Fin.tail w,fun i j=> by rw[show Fin.cons (0:ℝ) (Fin.tail w)=w from hc ▸ Fin.cons_self_tail w,he]; exact F.coords.apply_symm_apply _⟩
end YM.Trace.Margin
