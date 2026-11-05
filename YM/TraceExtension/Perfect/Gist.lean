import YM.TraceExtension.Perfect.Herald
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Asymptotics
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}
-- fixed shape oracle used both epochs
structure Slide (G:Gauge)(P:Patch)(Z:KernelChoices)(p:Clip)(μ A α V:ℝ) extends Lot G P Z p μ A where
    k : CrossA s.ratio.count
    t : s.Choices
    shade (l:List Axis)(h:l.length ≤ 3) : (advanceC s.ratio.count k l).strip α (V/(P.L.val:ℝ)^(1+l.length))
    color : Ether k
    guage : Guessed wood (installed s.ratio k) ρ
namespace Slide
variable {P:Patch}{Z:KernelChoices}{p:Clip}{μ A α B:ℝ} (X : Slide G P Z p μ A α B)
lemma coeff_len : X.s.ratio.count=P.L:= congr_arg Patch.L X.patch
def salon (v:Site X.f) := stampA X.s X.t (fresh X.wood X.ρ (installed X.s.ratio X.k) v)
def dig := stampA X.s X.t (liftedUp X.wood (installed X.s.ratio X.k) X.ρ)
lemma salon_pay (x:Site X.f): ContDiffAt ℝ ω (X.salon x) 0:=stampStanding X.t _ X.size.1 (fresh_thaw X.law _) (fresh_zero X.law x)
lemma dig_pay : ContDiffAt ℝ ω X.dig 0:= stampStanding X.t _ X.size.1 (liftedThaw X.law) (lift_origin X.law)
lemma salon_zero (x:Site X.f): X.salon x 0=0:= stamp_zero _ _ _ (fresh_zero X.law x)
lemma dig_zero : X.dig 0=0:= stamp_zero _ _ _ (lift_origin X.law)
lemma pillars(v:Site X.f)(x:pairA G X.f)(z:pairA G X.c) : fderiv ℝ (X.salon v) 0 (desk z) x=quilt X.s (of (fleece (installed X.s.ratio X.k) (X.s.ratio.count.val+1) v)) x z:= knit_fresh _ _ _ _ _ X.law X.size.1 X.guage X.price x z
lemma tender_pre {u S:ℝ}(t:ℕ)(h:0<u)(d:ℝ)(hd:0≤d)(he:d ≤ u)(x:Site X.f)(y:Site X.c)
   (ht:Settle (landW y) (landW x) (quilt (G:=G) X.s (of (fleece (installed X.s.ratio X.k) (X.s.ratio.count.val+1) x))) (amber X.s X.k x) (aquifer X.s X.k x) u t X.s.ratio.count.val S):
   Settle (landW y) (landW x) (fun a b=>fderiv ℝ (X.salon x) 0 (desk b) a) (amber X.s X.k x) (aquifer X.s X.k x) d t (P.L.val:ℝ) S:=by
 let K:=fun z: pairA G X.c=>landW y z
 have hv x (z:pairA G X.c→ℝ): sh K d t x z ≤ sh K u t x z:= Finset.sum_le_sum fun i _=>mul_le_mul_of_nonneg_right (spot_tiny _ _ _ _ hd he le_rfl) (norm_nonneg _)
 simp_rw [pillars]; rw [show P.L.val=X.s.ratio.count.val from congr_arg Subtype.val X.coeff_len.symm]
 exact ⟨fun i=> (hv ..).trans (ht.total i),fun i=> (hv ..).trans (ht.p i),fun i=>(hv ..).trans (ht.q i),fun i h=>(hv ..).trans (ht.near i h)⟩
variable (G μ A α B) in
lemma early (σ:ℝ)(h0:0<σ)(hσ:σ<α)(h:0≤B)(j t:ℕ)(T:ℝ)(hT:0≤T):
    ∃ C:ℝ,0 ≤ C ∧ ∀ (P:Patch) (Z:KernelChoices)(p:Clip) (X : Slide G P Z p μ A α B), P.J=j →8*(P.L.val+1)+4 ≤ X.f.val→ ∀ x y, (separation (X.s.ratio.embed y) x :ℝ) ≤ T*P.L.val → ∀ v:ℝ,0≤v→ v≤σ→
     Settle (landW y) (landW x) (fun a b=>fderiv ℝ (X.salon x) 0 (desk b) a) (amber X.s X.k x) (aquifer X.s X.k x) v t P.L.val C:=by
    obtain ⟨C,c,H⟩:=sparkle G σ α B T t j h0.le hσ hT h
    refine ⟨C,c,fun P Z p X he h x y hh v hv hp=>X.tender_pre t h0 _ hv hp x y ?_⟩
    rw [lantern_arr x]
    refine H _ _ X.s X.k ((congr_arg Patch.J X.patch).trans he) (fun l h=> ?_) (by rw [X.coeff_len]; exact h) y x (by rw [X.coeff_len]; exact hh)
    rw [show X.s.ratio.count.val=P.L.val from congr_arg Subtype.val X.coeff_len]; exact X.shade _ h
variable (G P Z p μ A α B) in
theorem early_uniform (K:ℝ)(hK:0 ≤ K)(hz:0<α)(n t:ℕ):∃ a C,0<a ∧ 0≤C∧∀ (X:Slide G P Z p μ A α B) x y, (separation (X.s.ratio.embed y) x:ℝ)≤K*P.L.val→∀ k j,k ≤ n→ ∀ v:ℝ,0≤v→ v≤a→ sail (X.salon x) 0 (landW y) k j v t ((↑(landW x j):ℝ)/P.L.val) ≤ C:=by
 let E:=Σ (s:Slide G P Z p μ A α B), Site s.f × Site s.c
 let T:={e:E // (separation (e.1.s.ratio.embed e.2.2) e.2.1:ℝ) ≤ K*P.L.val}
 let L (t:T):=t.val.fst
 let Y(i:T): Site (L i).c:=i.val.2.2
 let X(i:T): Site (L i).f:=i.val.2.1
 have hh:= Lot.paid_post (fun i:T=>(L i).toLot) (fun i=>(L i).k) X Y hz (v:=B) (fun i=> by simpa only[List.length_nil,add_zero,pow_one,advanceC] using (L i).shade [] (by simp)) (fun i=>(L i).t) K hK (fun i=> i.property) n t
 obtain ⟨a,C,ha,hc,H⟩:= hh.2; exact ⟨a,C,ha,hc,fun w x y hv=> fun k j hx=> H (⟨⟨w,(x,y)⟩,hv⟩) _ _ hx⟩
variable {W:Type}{F:Filter W} (X:W→Slide G P Z p μ A α B)(x:∀ w,Site (X w).c)(q:Cover)
lemma smooth_cost {H:∀ w,Acr G (X w).f→ℝ}{A':Tit G→Tit G→ℝ}{b:ℕ} (hA:∀ i j, ScoreG i+ScoreG j<b→ A' i j=0)
    (hp:Stoke F (fun w=> (X w).s.ratio.embed (x w)+wrap _ q) H A' b)(hH:∀ w,ContDiffAt ℝ ω (H w) 0)(hℓ:∀ w,fderiv ℝ (H w) 0=0)
    (hc:Tendsto (fun w=> (X w).c.val) F atTop)(he:0<α)(hV:0≤B)
    (t:ℕ)(ht:4≤t){σ Y:ℝ}(hσ:0<σ)(hv:0≤Y)(hu:∀ᶠ w in F,cost (landW ((X w).s.ratio.embed (x w)+wrap _ q)) σ t 0 (bank (iteratedFDeriv ℝ 2 (H w) 0))≤ Y): Stoke F x (fun w=>H w ∘ (X w).dig) (fun i j=> (((P.L.val:ℝ))⁻¹ ^ b) * A' i j) b :=by
 let V:=fun i:W=>liftedUp (X i).wood (installed (X i).s.ratio (X i).k) (X i).ρ
 have hz i:Teller (X i).s (X i).t p (X i).b 1 (1:Stationary.Joint G (X i).c (X i).f):= (Stationary.awake (X i).t (X i).price (U:=fun x:ℝ=> (1:Stationary.Joint G (X i).c (X i).f)) (Thaw.fixed 1 _) rfl (X i).size.1 root_customs).self_of_nhds
 apply crossing_step (fun w=> (X w).s) V (fun i=>(X i).t) P.L (fun i=>(X i).k) q x (fun i=>(X i).coeff_len) hz hc he (fun i=>(X i).size.1) (show 0 ≤ B/(P.L.val:ℝ) from div_nonneg hV (side_pos _).le) (fun i=>liftedThaw (X i).law) (fun i=>lift_origin (X i).law) ?_ (fun i=>(X i).color) (fun i=>smooth_plan (X i).law (X i).size.1 (X i).t (X i).guage) _ hA hp hH hℓ (fun i=>(X i).dig_pay) _ ht hσ hv hu
 intro w; have he:=(X w).shade [] (by simp);simpa only [advanceC,List.length_nil,add_zero,pow_one,(X w).coeff_len] using he

end Slide
end YM.Trace.Perfect
