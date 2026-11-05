import YM.Planned.PRIMARY_INTEGRAL_295.Flairs
/-!
# Gram transforms under posed render. No phase reindex here

Works even in canonical partial p windows and upper labels for conditional
physical test. Assuming branch wells. Canvas.Delta ancestor debts force budgets
separately. Sensor Φ transformations strictly equality Gram on FULL torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Pomp
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks Night Hives Candles Barges Hoods Flairs
open Next.Fluctuations Work.E03
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G:Gauge} {c f : Side} {S:StepData c f}
variable (K:Core G S)(z:Site c→G.El)(V:Config G c) (hb:S.patch.Branches S.kernel G)

def hero:= family (Drops c f) G
def posate(z:Site c→G.El) := z ∘ shade S

section
omit hb in
lemma lawn (a:Temps G f)(i:Seats G c f) : (dowel K V).mulVec a i= ballast * keel K i.1 V a i.2:= by
   let F:= keel K i.1 V; let L : G.Color→L[ℝ] ℝ:= EuclideanSpace.proj i.2
   change _=ballast * L (F a)
   have hx : (∑ i:Acres f G, a i • (Pi.single i 1 : Temps G f))=a:=by ext i; simp [Pi.single_apply, Finset.sum_apply]
   nth_rw 2 [← hx]; rw [map_sum,map_sum,mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [map_smul,map_smul]
   change ballast * L (F _) * a j= ballast * (a j * L (F (Pi.single j 1))) ; ring

include hb
lemma shackle (x:Drops c f)(a:Temps G f) :
     keel K x (Lattice.gauge z V) (harvest.burn (flatten (S:=S) z) a)= G.adjoint (z (shade S x)) (keel K x V a) :=by
   let q:= bend (z (shade S x)); let U : Temps G f≃L[ℝ] Temps G f:= LinearEquiv.toContinuousLinearEquiv
       (Hive.swab harvest (flatten (S:=S) z))
   have he : logs K x (Lattice.gauge z V) ∘ U= q ∘ logs K x V:=funext (fun y=> (strings K V z x hb).2 y)
   have hy := congr_arg (fderiv ℝ · (0:Temps G f)) he
   rw [U.comp_right_fderiv,q.comp_fderiv,map_zero] at hy
   exact DFunLike.congr_fun hy a

lemma charming : Crown hero harvest (posate (S:=S) z) (flatten (S:=S) z) (dowel K V) (dowel K (Lattice.gauge z V)):=by
   let z':=posate (S:=S) z; let T:= Lattice.gauge z V; let q:=flatten (S:=S) z
   have ht (a:Temps G f) : (hero.burn z') ((dowel K V).mulVec a) = (dowel K T).mulVec (harvest.burn q a):=by
     ext i
     rw [lawn K T]
     set p:= i.1; set j:= i.2
     have he' : hero.bunch ((dowel K V).mulVec a) i = ballast • keel K p V a :=by
       apply PiLp.ext; intro k; exact lawn K V a (p,k)
     change G.adjoint (z (shade S p)) (hero.bunch _ i) j = _
     rw [he',map_smul,shackle K z V hb]; rfl
   have hy(a:Temps G f) : (hero.paint z' * dowel K V).mulVec a= (dowel K T* harvest.paint q).mulVec a:=by
     rw [←mulVec_mulVec,←mulVec_mulVec,Hive.pigment,Hive.pigment,ht]
   ext i j; exact (show _ from by simpa only [mulVec_single_one,col_apply] using congr_fun (hy (Pi.single j 1)) i)

omit V hb in
lemma icicles : Crown harvest harvest (flatten (S:=S) z) (flatten (S:=S) z) K.fires K.fires:=by
   unfold Crown
   let z':= flatten (S:=S) z; let H:= (harvest (G:=G) (f:=f)).paint z'
   ext i j; unfold fires; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
   by_cases hh:i.1=j.1
   · rw [hh,mul_comm]
   have hv := (Hive.tone harvest z' i j (show Hive.room (harvest (G:=G) (f:=f)) i≠_ from hh)); change H i j * _= _*H i j; change H i j=0 at hv; rw [hv,zero_mul,mul_zero]

/-- Full DERIVED gram coherence of world. b here unnormalized global foams p.
    Applies to P.Mode when account paid for actual K inputs. -/
lemma kernels :
     Crown harvest harvest (flatten (S:=S) z) (flatten (S:=S) z) (dark K V) (dark K (Lattice.gauge z V)) ∧
     foams K (Lattice.gauge z V)= harvest.burn (flatten (S:=S) z) (foams K V):=by
   let z':=posate (S:=S) z; let T:=Lattice.gauge z V
   have h := charming K z V hb
   refine ⟨(h.push.donate h).add (icicles K z),?_⟩
   unfold foams; rw [h.push.miles]
   apply congr_arg
   ext i; let p:= i.1; let j:=i.2
   unfold F₀
   have hp : hero.bunch (F₀ K V) i= ballast • garth K p V:=by apply PiLp.ext; intro k; rfl
   change _= G.adjoint (z (shade S p)) (hero.bunch (F₀ K V) i) j
   rw [hp,map_smul,(strings K V z i.1 hb).1]; rfl
end
end YM.Planned.PrimaryIntegral295.Pomp
