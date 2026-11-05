import YM.RG08.Atrium.Zebra
/-!
# Coordinate algebra of formal mark: Ambient matrix acts on Graded portfolios (slot filtration)
 unit telescope and normalization. all power series. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Atrium
open Function Finset Jetty Lattice Isles Forms Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Spar Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Yurt Halo Trill
open RG Precision Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius PowerSeries Matrix
variable {G:Gauge}{d n p l e D k:ℕ}
local notation "E₀"=>Ed G Cover
variable (X:Labels.Frame G d)
abbrev Playbook:=Matrix (Accent X) (Accent X) Dig
abbrev Bouquet:=Accent X→GrainS (Ed G Cover)
variable {X}
local notation "A₀"=>Accent X
-- arity and joint h (do not confuse X.grades)
def octave (i:A₀):ℕ:= (X.grades i.ear).2
def gamut (i:A₀):ℕ:= (X.grades i.ear).1+Trill.weight i.test.play
@[simp] lemma octave_le (i:A₀):octave i≤d:=(Trill.grades_two ..).trans (Labels.Frame.bound ..)
@[simp] lemma gamut_le (i:A₀):gamut i≤d:=i.joint

def Cloth (M:Playbook X):Prop:=∀ i j:A₀,Paces (octave i) (octave j) (M i j)
def Threads (D:ℕ)(S:Bouquet X):Prop:=∀ i,Folk D (octave i) (S i)

def shuffle (M:Playbook X)(S:Bouquet X):Bouquet X:=fun i=>∑ j:A₀,Atrium.slip (M j i) (S j)
lemma cloth_threads {S:Bouquet X}{M:Playbook X}(ht:Cloth M)(h:Threads D S):Threads D (shuffle M S):=fun i=>Folk.tots (s:=univ) fun j _=> Folk.slip (ht j i) (h j)
lemma cloth_one:Cloth (1:Playbook X):=by
 intro i j;rw [Matrix.one_apply];split_ifs with h;subst j; exact Paces.church le_rfl _; exact Paces.nothing
lemma Cloth.sew {M N:Playbook X}(hm:Cloth M)(hn:Cloth N):Cloth (M*N):=by
 intro i j;rw [Matrix.mul_apply];apply Paces.sum;intro k _;rw [mul_comm];exact (hn k j).mul (hm i k)
lemma cloth_empty : Cloth (0:Playbook X):=fun _ _=> Paces.nothing
lemma shuffle_one (S:Bouquet X):shuffle 1 S=S:=by funext i; unfold shuffle; simp_rw [Matrix.one_apply];rw [sum_eq_single i];simp [slip_one];intro b hb h;simp [h,slip_zero];simp
lemma mingle (S:Bouquet X)(Q N:Playbook X):shuffle N (shuffle Q S)=shuffle (Q*N) S:=by
 unfold shuffle;funext i
 simp_rw [Matrix.mul_apply,slip_family,slip_family',slip_stunt];rw [sum_comm];apply sum_congr rfl;intro _ _;apply sum_congr rfl;intro _ _; rw [mul_comm]

def ask (S:Bouquet X):Playbook X:=Matrix.of fun i j=> Atrium.ballot (S j) i -- chart i uses output normalization
lemma asking (S:Bouquet X)(M:Playbook X)(h:Threads D S)(he:Cloth M):ask (shuffle M S)=ask S * M:=by
 ext i j :1;change ballot (∑ k:A₀,Atrium.slip (M k j) (S k)) i=_
 rw [show (∑ k:A₀,Atrium.slip (M k j) (S k))=∑ k:A₀,(1:ℝ) • Atrium.slip (M k j) (S k) from by simp,relieved _ _ _ (fun c _ _ _=>permit_ready (Folk.slip (he c j) (h c)).1)]
 rw [Matrix.mul_apply];apply sum_congr rfl;intro k _;rw [one_smul,voted _ _ (S k) (fun i n=>Trill.permit_ready (h k).inlet),mul_comm];rfl
lemma cloth_request (S:Bouquet X)(h:Threads D S):Cloth (ask S):=fun i j=>ballot_slow (S j) (h j).inlet.lit i
lemma standardized (H:Source.Hol G)(T:SectionData X)(h:T.Sound H)(hb:Bid.pop T)(hd:d≤D):Threads D (Fete.encore T)∧ask (Fete.encore T)=1:=by
 refine ⟨fun i=>⟨Fete.encore_permit T i hd,Fete.encore_calls T H h hb i⟩,?_⟩;ext i j:1;rw [Matrix.one_apply];ext e:1
 change tap e (ballot (Fete.encore T j) i)=PowerSeries.coeff _ _
 rw [ballot_value,Fete.encore_project T h hb];by_cases hx:i=j;subst j;simp only [and_true,if_true,PowerSeries.coeff_one];simp [hx,Ne.symm hx]

-- trivial integration Frame solve once step & inverse certification supplied. Calendar shape F.H.Mesh consumed later. This def endpoint is algebraic not quantitative.
def dressed (L:Bouquet X→Bouquet X)(S:Bouquet X):Playbook X:=ask (L S)
lemma normalized (L:Bouquet X→Bouquet X)(S:Bouquet X)(M:Playbook X)(hL:Threads D (L S))(hM:Cloth M)(hR:dressed L S*M=1)(hR':M*dressed L S=1):
 let U:=shuffle M (L S)
 ; Threads D U ∧ ask U=1 ∧ L S= shuffle (dressed L S) U :=by
 intro U
 refine ⟨cloth_threads hM hL,asking (L S) M hL hM|>.trans hR,?_⟩;unfold U;rw [mingle,hR',shuffle_one]
end YM.RG08.Atrium
