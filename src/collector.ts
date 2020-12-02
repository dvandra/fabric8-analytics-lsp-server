/* --------------------------------------------------------------------------------------------
 * Copyright (c) Pavel Odvody 2016
 * Licensed under the Apache-2.0 License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */
'use strict';
import { Stream } from 'stream';
import * as Xml2Object from 'xml2object';
import * as jsonAst from 'json-to-ast';
import { IPosition, IKeyValueEntry, KeyValueEntry, Variant, ValueType } from './types';
import { stream_from_string, getGoLangImportsCmd } from './utils';
import { config } from './config';
import { exec } from 'child_process';

/* Please note :: There was issue with semverRegex usage in the code. During run time, it extracts 
 * version with 'v' prefix, but this is not be behavior of semver in CLI and test environment. 
 * At the moment, using regex directly to extract version information without 'v' prefix. */
//import semverRegex = require('semver-regex');
function semVerRegExp(line: string): RegExpExecArray {
    const regExp = /(?<=^v?|\sv?)(?:0|[1-9]\d*)\.(?:0|[1-9]\d*)\.(?:0|[1-9]\d*)(?:-(?:0|[1-9]\d*|[\da-z-]*[a-z-][\da-z-]*)(?:\.(?:0|[1-9]\d*|[\da-z-]*[a-z-][\da-z-]*))*)?(?:\+[\da-z-]+(?:\.[\da-z-]+)*)?(?=$|\s)/ig
    return regExp.exec(line);
}

/* String value with position */
interface IPositionedString {
  value:    string;
  position: IPosition;
}

/* Dependency specification */
interface IDependency {
  name:    IPositionedString;
  version: IPositionedString;
}

/* Dependency collector interface */
interface IDependencyCollector {
  classes: Array<string>;
  collect(contents: string): Promise<Array<IDependency>>;
}

/* Dependency class that can be created from `IKeyValueEntry` */
class Dependency implements IDependency {
  name:    IPositionedString;
  version: IPositionedString;
  constructor(dependency: IKeyValueEntry) {
    this.name = {
        value: dependency.key,
        position: dependency.key_position
    };
    this.version = {
        value: dependency.value.object,
        position: dependency.value_position
    };
  }
}

class NaivePyParser {
    constructor(contents: string) {
        this.dependencies = NaivePyParser.parseDependencies(contents);
    }

    dependencies: Array<IDependency>;

    static parseDependencies(contents:string): Array<IDependency> {
        const requirements = contents.split("\n");
        return requirements.reduce((dependencies, req, index) => {
            // skip any text after #
            if (req.includes('#')) {
                req = req.split('#')[0];
            }
            const parsedRequirement: Array<string>  = req.split(/[==,>=,<=]+/);
            const pkgName:string = (parsedRequirement[0] || '').trim();
            // skip empty lines
            if (pkgName.length > 0) {
                const version = (parsedRequirement[1] || '').trim();
                const entry: IKeyValueEntry = new KeyValueEntry(pkgName, { line: 0, column: 0 });
                entry.value = new Variant(ValueType.String, version);
                entry.value_position = { line: index + 1, column: req.indexOf(version) + 1 };
                dependencies.push(new Dependency(entry));
            }
            return dependencies;
        }, []);
    }

    parse(): Array<IDependency> {
        return this.dependencies;
    }
}

/* Process entries found in the txt files and collect all dependency
 * related information */
class ReqDependencyCollector implements IDependencyCollector {
    constructor(public classes: Array<string> = ["dependencies"]) {}

    async collect(contents: string): Promise<Array<IDependency>> {
        let parser = new NaivePyParser(contents);
        return parser.parse();
    }

}

class NaiveGomodParser {
    constructor(contents: string, goImports: Set<string>) {
        this.dependencies = NaiveGomodParser.parseDependencies(contents, goImports);
    }

    dependencies: Array<IDependency>;

    static getReplaceMap(line: string, index: number): any{
        // split the replace statements by '=>'
        const parts: Array<string> = line.replace('replace', '').replace('(', '').replace(')', '').trim().split('=>');
        const replaceWithVersion = semVerRegExp(parts[1]);

        // Skip lines without final version string
        if (replaceWithVersion && replaceWithVersion.length > 0) {
            const replaceTo: Array<string> = (parts[0] || '').trim().split(' ');
            const replaceToVersion = semVerRegExp(replaceTo[1]);
            const replaceWith: Array<string> = (parts[1] || '').trim().split(' ');
            const replaceWithIndex = line.lastIndexOf(parts[1]);
            const replaceEntry: IKeyValueEntry = new KeyValueEntry(replaceWith[0].trim(), { line: 0, column: 0 });
            replaceEntry.value = new Variant(ValueType.String, 'v' + replaceWithVersion[0]);
            replaceEntry.value_position = { line: index + 1, column: (replaceWithIndex + replaceWithVersion.index) };
            const replaceDependency = new Dependency(replaceEntry);
            const isReplaceToVersion: boolean = replaceToVersion && replaceToVersion.length > 0;
            return {key: replaceTo[0].trim() + (isReplaceToVersion ? ('@v' + replaceToVersion[0]) : ''), value: replaceDependency};
        }
        return null;
    }

    static  applyReplaceMap(dep: IDependency, replaceMap: Map<string, IDependency>): IDependency {
        let replaceDependency = replaceMap.get(dep.name.value + "@" + dep.version.value);
        if (replaceDependency === undefined) {
            replaceDependency = replaceMap.get(dep.name.value);
            if(replaceDependency === undefined) {
                return dep;
            }
        }
        return replaceDependency;
    }

    static parseDependencies(contents:string, goImports: Set<string>): Array<IDependency> {
        let replaceMap = new Map<string, IDependency>();
        let goModDeps = contents.split("\n").reduce((dependencies, line, index) => {
            // skip any text after '//'
            if (line.includes("//")) {
                line = line.split("//")[0];
            }
            if (line.includes("=>")) {
                let replaceEntry = NaiveGomodParser.getReplaceMap(line, index);
                if (replaceEntry) {
                    replaceMap.set(replaceEntry.key, replaceEntry.value);
                }
            } else {
                // Not using semver directly, look at comment on import statement.
                //const version = semverRegex().exec(line)
                const version = semVerRegExp(line);
                // Skip lines without version string
                if (version && version.length > 0) {
                    const parts: Array<string> = line.replace('require', '').replace('(', '').replace(')', '').trim().split(' ');
                    const pkgName: string = (parts[0] || '').trim();
                    // Ignore line starting with replace clause and empty package
                    if (pkgName.length > 0) {
                        const entry: IKeyValueEntry = new KeyValueEntry(pkgName, { line: 0, column: 0 });
                        entry.value = new Variant(ValueType.String, 'v' + version[0]);
                        entry.value_position = { line: index + 1, column: version.index };
                        // Push all direct and indirect modules present in go.mod (manifest) 
                        dependencies.push(new Dependency(entry));
                    }
                }
            }
            return dependencies;
        }, []);

        let goPackageDeps = [];

        goImports.forEach(importStatement => {
            let exactMatchDep: Dependency = null;
            let moduleMatchDep: Dependency = null;
            goModDeps.forEach(goModDep => {
                if (importStatement == goModDep.name.value) {
                    // Software stack uses the module
                    exactMatchDep = goModDep;
                } else if (importStatement.startsWith(goModDep.name.value + "/")) {
                    // Find longest module name that matches the import statement
                    if (moduleMatchDep == null) {
                        moduleMatchDep = goModDep;
                    } else if (moduleMatchDep.name.value.length < goModDep.name.value.length) {
                        moduleMatchDep = goModDep;
                    }
                }
            });

            if (exactMatchDep == null && moduleMatchDep != null) {
                // Software stack uses a package from the module
                let replaceDependency = NaiveGomodParser.applyReplaceMap(moduleMatchDep, replaceMap);
                if (replaceDependency !== moduleMatchDep) {
                    importStatement = importStatement.replace(moduleMatchDep.name.value, replaceDependency.name.value);
                }
                const entry: IKeyValueEntry = new KeyValueEntry(importStatement + '@' + replaceDependency.name.value, replaceDependency.name.position);
                entry.value = new Variant(ValueType.String, replaceDependency.version.value);
                entry.value_position = replaceDependency.version.position;
                goPackageDeps.push(new Dependency(entry));
            }
        });

        goModDeps = goModDeps.map(goModDep => NaiveGomodParser.applyReplaceMap(goModDep, replaceMap));

        // Return modules present in go.mod and packages used in imports.
        return [...goModDeps, ...goPackageDeps];
    }

    parse(): Array<IDependency> {
        return this.dependencies;
    }
}

/* Process entries found in the go.mod file and collect all dependency
 * related information */
class GomodDependencyCollector implements IDependencyCollector {
    constructor(private manifestFile: string, public classes: Array<string> = ["dependencies"]) {
        this.manifestFile = manifestFile;
    }

    async collect(contents: string): Promise<Array<IDependency>> {
        let promiseExec = new Promise<Set<string>>((resolve, reject) => {
            const vscodeRootpath = this.manifestFile.replace("file://", "").replace("/go.mod", "")
            exec(getGoLangImportsCmd(),
                { cwd: vscodeRootpath, maxBuffer: 1024 * 1200 }, (error, stdout, stderr) => {
                if (error) {
                    if (error.code == 127) { // Invalid command, go executable not found
                        reject(`Unable to locate '${config.golang_executable}'`);
                    } else {
                        reject(`Unable to execute '${config.golang_executable} list' command, run '${config.golang_executable} mod tidy' to know more`);
                    }
                } else {
                    resolve(new Set(stdout.toString().split("\n")));
                }
            });
        });
        const goImports: Set<string> = await promiseExec;
        let parser = new NaiveGomodParser(contents, goImports);
        return parser.parse();
    }

}

class NaivePomXmlSaxParser {
    constructor(stream: Stream) {
        this.stream = stream;
        this.parser = this.createParser();
    }

    stream: Stream;
    parser: Xml2Object;
    dependencies: Array<IDependency> = [];
    isDependency: boolean = false;
    versionStartLine: number = 0;
    versionStartColumn: number = 0;

    createParser(): Xml2Object {
        let parser = new Xml2Object([ "dependency" ], {strict: true, trackPosition: true});
        let deps = this.dependencies;
        let versionLine = this.versionStartLine;
        let versionColumn = this.versionStartColumn;

        parser.on("object", function (name, obj) {
            if (obj.hasOwnProperty("groupId") && obj.hasOwnProperty("artifactId") && obj.hasOwnProperty("version") && 
                (!obj.hasOwnProperty("scope") || (obj.hasOwnProperty("scope") && obj["scope"] != "test"))) {
                let ga = `${obj["groupId"]}:${obj["artifactId"]}`;
                let entry: IKeyValueEntry = new KeyValueEntry(ga, {line: 0, column: 0});
                entry.value = new Variant(ValueType.String, obj["version"]);
                entry.value_position = {line: versionLine, column: versionColumn};
                let dep: IDependency = new Dependency(entry);
                deps.push(dep)
            }
        });
        parser.saxStream.on("opentag", function (node) {
            if (node.name == "dependency") {
                this.isDependency = true;
            }
            if (this.isDependency && node.name == "version") {
                versionLine = parser.saxStream._parser.line + 1;
                versionColumn = parser.saxStream._parser.column +1;
            }
        });
        parser.saxStream.on("closetag", function (nodeName) {
            // TODO: nested deps!
            if (nodeName == "dependency") {
                this.isDependency = false;
            }
        });
        parser.on("error", function (e) {
            // the XML document doesn't have to be well-formed, that's fine
            parser.error = null;
        });
        parser.on("end", function () {
            // the XML document doesn't have to be well-formed, that's fine
            // parser.error = null;
            this.dependencies = deps;
        });
        return parser
    }

    async parse() {
        return new Promise(resolve => {
            this.stream.pipe(this.parser.saxStream).on('end', (data) => {
                resolve(this.dependencies);
           });
        });

    }
}

class PomXmlDependencyCollector implements IDependencyCollector {
    constructor(public classes: Array<string> = ["dependencies"]) {}

    async collect(contents: string): Promise<Array<IDependency>> {
        const file = stream_from_string(contents);
        let parser = new NaivePomXmlSaxParser(file);
        let dependencies;
         await parser.parse().then(data => {
            dependencies = data;
        });
        return dependencies || [];
    }
}

class PackageJsonCollector implements IDependencyCollector {
    constructor(public classes: Array<string> = ["dependencies"]) {}

    async collect(contents: string): Promise<Array<IDependency>> {
      const ast = jsonAst(contents);
      return ast.children.
              filter(c => this.classes.includes(c.key.value)).
              flatMap(c => c.value.children).
              map(c => {
                  let entry: IKeyValueEntry = new KeyValueEntry(c.key.value, {line: c.key.loc.start.line, column: c.key.loc.start.column + 1});
                  entry.value = new Variant(ValueType.String, c.value.value);
                  entry.value_position = {line: c.value.loc.start.line, column: c.value.loc.start.column + 1};
                  return new Dependency(entry);
              });
    }
}

export { IDependencyCollector, PackageJsonCollector, PomXmlDependencyCollector, ReqDependencyCollector, GomodDependencyCollector, IPositionedString, IDependency };
