import YM.MergeProof.South.Sand

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent  PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
local notation "ζ!"=> ζ d
section
variable {I:Type}[Fintype I][DecidableEq I]
variable (X:Extra.Histories.Music (C.labels.level d) C.path N p) (Z:Option I→∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)) (v:I→ C.label d)(s:I→ℂ)(b:C.label d)(L:I→C.label d)(Q:Coefficient (C.labels.level d) (C.side k p))
local notation "exp'"=> fun (x:Coefficient (C.labels.level d) (C.side k p))=> x.exponentialEntry 0 (C.localSection d) (R k)
local notation "pro"=> fun (x:Coefficient (C.labels.level d) (C.side k p))=> profile (R k).activities x.forced
local notation "F'"=> fun i:Option I=> Z i k
local notation "l"=> fun i => Extra.Histories.primary (0:Site (C.side k p)) (L i)
local notation "p!"=> (X.tone k).plays
variable (a:Motion)(o:∀ m, Site (C.side m p))
local notation "T!"=> alto T k d
local notation "x"=> fun (i:Option I)=>Option.elim i (1:ℂ) (fun j=>Motion.scalar a (-s j))
lemma plush (hK:ℓ ≤ k)(hN:k≤N) (hX:Sung Y! T N p C.params W ℓ X) (hb:b=∑ i,s i • v i) (he:exp' (Z none k)= exp' Q+ exp' (p! (-b))) (hσ:∀ i:I,exp' (Z (some i) k)= exp' (l i) + exp' (p! (-(v i)))) (hk:pro (Z none k)= pro Q+ pro (p! (-b))) (hρ:∀ i:I, pro (Z (some i) k)= pro (p! (-(v i)))) : (∑ i, x i • liftF T Y! N p a o (Z i) k)= radiant T! a (o k) (exp' Q)+stepUp a (o k) (∑ i,(-s i) • lens C N k p d (L i)) ∧ (∑ i,x i • liftK T N p a o (Z i) k)= sunny (R k) Q.forced a (o k) T!:=by
    have hT:= hX.earned k hK hN
    let p':= (X.tone k); let η (w:C.label d):=exp' (p! w); let θ (w:C.label d):=pro (p! w); have ht:IsLinearMap ℂ η:=expoLinear p'.plays p'.charge hT.book (fun i=>(hT.earns i).2)
    have hy:IsLinearMap ℂ θ:=inkL p'.plays p'.charge hT.book (fun i=>(hT.earns i).2)
    -- -b + sum -s*(-v)=0
    have hr: -b + ∑ i, (-s i) • (-v i)=0:=by rw [hb];simp
    have hW: (∑ i:Option I, (Option.elim i (1:ℂ) (fun j=>-s j)) • exp' (Z i k))= exp' Q + ∑ i, -s i • exp' (l i):=by
        rw [Fintype.sum_option]; simp only [Option.elim,one_smul,hσ,smul_add,he,Finset.sum_add_distrib]
        let A:= IsLinearMap.mk' η ht; have hp : exp' (p! (-b))+ ∑ i,(-s i) • exp' (p! (-v i))=0:=by
            change A (-b)+∑ i, (-s i) • A (-v i)=0
            simp_rw [← map_smul];rw [← map_sum, ← map_add,hr,map_zero]
        dsimp only at hp; rw [eq_neg_of_add_eq_zero_left hp]; abel
    have hΛ : (∑ i:Option I,(Option.elim i (1:ℂ) (fun j=>-s j)) • pro (Z i k))=pro Q:=by
        rw [Fintype.sum_option]; simp only [Option.elim,hk,hρ,one_smul]
        let A:= IsLinearMap.mk' θ hy; have hp : pro (p! (-b))+∑ i,(-s i) • pro (p! (-v i))=0:=by
            change A (-b)+∑ i, (-s i) • A (-v i)=0; simp_rw [← map_smul];rw [← map_sum, ← map_add,hr,map_zero]
        dsimp only at hp; rw [eq_neg_of_add_eq_zero_left hp]; abel
    let τ:Config G (C.side k p)→ Config G (C.side k p):=pull a.1 (o k)
    let g:=fun i:Option I=>Option.elim i (1:ℂ) (fun j=>-s j); have hx(i:Option I): scalar a (g i)=x i:=by cases i;unfold scalar; split <;>simp [g];rfl
    have hU{J:Type}[Fintype J](g:J→ℂ): scalar a (∑ i,g i)=∑ i,scalar a (g i):=by unfold scalar; split;exact star_sum ..;rfl
    constructor
    · have hp(j): T! • exp' (l j)= lens C N k p d (L j):=rfl
      rw [show (∑ i, x i • liftF T Y! N p a o (Z i) k)=stepUp a (o k) (T! • ∑ i,g i • (exp' (Z i k))) from funext fun i=> by
         simp only [liftF,radiant,stepUp, Pi.smul_apply,Finset.sum_apply, smul_eq_mul]; rw [lept,hU]; simp only [scalar_mul,hx,Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=> mul_left_comm ..]
      change stepUp _ _ (_ • ∑ i,g i • exp' (Z i k))= _; unfold g; rw [hW,smul_add,Finset.smul_sum]; simp_rw [smul_comm (alto T k d) (- s _),hp]
      funext i; unfold radiant stepUp; simp only [Pi.smul_apply,Pi.add_apply, scalar_add,smul_eq_mul,lept]
    change _ = T! • floatUp a (o k) (pro Q)
    rw [← hΛ]; unfold liftK sunny floatUp stepUp; funext i U; simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,hU,scalar_mul, ← hx,Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=> mul_left_comm ..
end
end YM.MergeProof
